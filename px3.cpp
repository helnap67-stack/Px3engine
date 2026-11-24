/*  PX 3 - C++ chess engine for ChessPX (drop-in replacement for PX 2, same WebAssembly ABI)
 *
 *  Exports : px_init(), px_io(), px_search(), px_perft(depth)
 *  Imports : env.px_now() -> f64   (milliseconds clock)
 *  I/O     : one int32[8192] block returned by px_io(), layout identical to PX 2 (see ChessPX worker):
 *     in : [0..63] board (a8 first; 0 empty, 1..6 = P N B R Q K white, +8 black)  [64] side (0 w,1 b)
 *          [65] castling bits wK=1 wQ=2 bK=4 bQ=8   [66] ep target (-1 none)   [67] halfmove   [68] fullmove
 *          [69] mode (0 random, 1 skill levels, 2 full strength)  [70] ms  [71] max depth  [72] qsearch depth
 *          [73] T*1000  [74] oops*1000  [75] mate*1000  [76] style  [77] seed  [78] n repeats
 *          [100 + i*67 ...] earlier positions (same 67-int layout) that can still repeat
 *     out: [0] from  [1] to  [2] promo (2..5)  [3] score cp  [4] depth  [5] nodes  [6] 1 = move found
 *
 *  Freestanding on purpose: no libc, no malloc, no exceptions, no libm.
 *  Build: see build.sh.  Native test build: see test_px3.cpp.
 */
#ifndef PX_TT_BITS
#define PX_TT_BITS 21                       /* 2^21 entries * 12 bytes = 24 MB */
#endif
typedef unsigned long long U64; typedef unsigned int U32; typedef unsigned short U16; typedef unsigned char U8; typedef short I16;

#if defined(__wasm__)
#define PX_EXPORT(n) extern "C" __attribute__((used, visibility("default"), export_name(#n)))
extern "C" __attribute__((import_module("env"), import_name("px_now"))) double px_now(void);
#else
#include <time.h>
#define PX_EXPORT(n) extern "C"
extern "C" double px_now(void){ timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1000.0 + t.tv_nsec * 1e-6; }
#endif

enum { WHITE = 0, BLACK = 1 };
enum { PAWN = 0, KNIGHT, BISHOP, ROOK, QUEEN, KING };
enum { NOPC = 12 };
#define MATE 30000
#define MATE_BOUND 29600
#define INFV 32000
#define MAXPLY 128
static const U64 FILE_A = 0x0101010101010101ULL, FILE_H = FILE_A << 7;
static const U64 RANK_1 = 0xFFULL, RANK_3 = RANK_1 << 16, RANK_6 = RANK_1 << 40, RANK_8 = RANK_1 << 56;
static const int PVAL[6] = { 100, 320, 330, 500, 900, 0 };

static inline int lsb(U64 b){ return __builtin_ctzll(b); }
static inline int msb(U64 b){ return 63 - __builtin_clzll(b); }
static inline int popc(U64 b){ return __builtin_popcountll(b); }
static inline int poplsb(U64& b){ int s = lsb(b); b &= b - 1; return s; }
static inline int imin(int a, int b){ return a < b ? a : b; }
static inline int imax(int a, int b){ return a > b ? a : b; }
static inline int iabs(int a){ return a < 0 ? -a : a; }

/* ---- tiny math (no libm in a freestanding wasm build) ---- */
static double pxlog(double x){ int k = 0; while(x >= 2){ x *= 0.5; k++; } while(x < 1){ x *= 2; k--; }
  double y = (x - 1) / (x + 1), y2 = y * y;
  return 2 * y * (1 + y2 * (1.0/3 + y2 * (1.0/5 + y2 * (1.0/7 + y2 * (1.0/9 + y2 / 11))))) + k * 0.6931471805599453; }
static double pxexpneg(double x){ /* exp(-x), x >= 0 */
  if(x > 60) return 0; int k = (int)(x * 1.4426950408889634); double r = x - k * 0.6931471805599453;
  double e = 1 - r * (1 - r / 2 * (1 - r / 3 * (1 - r / 4 * (1 - r / 5 * (1 - r / 6)))));
  while(k-- > 0) e *= 0.5; return e; }

/* ---- tables ---- */
static U64 PATT[2][64], NATT[64], KATT[64], FILEBB[8], ADJF[8], PASSM[2][64], OUTP[2][64];
static U64 ZOB[12][64], ZCAST[16], ZEP[8], ZSIDE;
static int CMASK[64];
static int PSQ_MG[12][64], PSQ_EG[12][64];
static int LMRT[64][64];
static bool inited = false;

static U64 rngS = 0x9E3779B97F4A7C15ULL;
static inline U64 rnd64(){ rngS ^= rngS >> 12; rngS ^= rngS << 25; rngS ^= rngS >> 27; return rngS * 2685821657736338717ULL; }
static inline double rnd01(){ return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

struct Magic { U64 mask, magic; U64* att; int shift; };
static Magic RM[64], BM[64];
static U64 rookTbl[102400], bishTbl[5248];
static inline U64 rookAtt(int s, U64 occ){ const Magic& m = RM[s]; return m.att[((occ & m.mask) * m.magic) >> m.shift]; }
static inline U64 bishopAtt(int s, U64 occ){ const Magic& m = BM[s]; return m.att[((occ & m.mask) * m.magic) >> m.shift]; }

static U64 slideRef(int sq, U64 occ, bool rook){
  static const int dr[8] = {1,-1,0,0,1,1,-1,-1}, dc[8] = {0,0,1,-1,1,-1,1,-1};
  U64 a = 0; int r0 = sq >> 3, c0 = sq & 7;
  for(int d = rook ? 0 : 4; d < (rook ? 4 : 8); d++){
    int r = r0 + dr[d], c = c0 + dc[d];
    while(r >= 0 && r < 8 && c >= 0 && c < 8){ U64 b = 1ULL << (r * 8 + c); a |= b; if(occ & b) break; r += dr[d]; c += dc[d]; } }
  return a; }

static void initMagics(bool rook){
  static const int SEEDS[8] = { 728, 10316, 55013, 32803, 12281, 15100, 16645, 255 };
  static U64 occ[4096], ref[4096]; static int epoch[4096]; int ep = 0; U64* pool = rook ? rookTbl : bishTbl; int off = 0;
  for(int sq = 0; sq < 64; sq++){
    Magic& m = rook ? RM[sq] : BM[sq];
    U64 edges = ((RANK_1 | RANK_8) & ~(RANK_1 << ((sq >> 3) * 8))) | ((FILE_A | FILE_H) & ~(FILE_A << (sq & 7)));
    m.mask = slideRef(sq, 0, rook) & ~edges; int bits = popc(m.mask); m.shift = 64 - bits; m.att = pool + off; off += 1 << bits;
    int n = 0; U64 b = 0; do { occ[n] = b; ref[n] = slideRef(sq, b, rook); n++; b = (b - m.mask) & m.mask; } while(b);
    rngS = SEEDS[sq >> 3] * 0x9E3779B97F4A7C15ULL + 12345;
    for(;;){
      U64 mg = rnd64() & rnd64() & rnd64(); if(popc((m.mask * mg) >> 56) < 6) continue;
      ep++; bool ok = true;
      for(int i = 0; i < n && ok; i++){ int idx = (int)((occ[i] * mg) >> m.shift);
        if(epoch[idx] != ep){ epoch[idx] = ep; m.att[idx] = ref[i]; } else if(m.att[idx] != ref[i]) ok = false; }
      if(ok){ m.magic = mg; break; } } } }

static void initPST(){
  static const int MGV[6] = { 82, 337, 365, 477, 1025, 0 }, EGV[6] = { 94, 281, 297, 512, 936, 0 };
  static const int MGP[8] = { 0, -8, -6, 2, 14, 32, 60, 0 }, EGP[8] = { 0, 0, 4, 10, 22, 45, 80, 0 };
  static const int KBACK[8] = { 0, 16, 6, -14, -14, -4, 22, 6 };
  for(int sq = 0; sq < 64; sq++){
    int f = sq & 7, r = sq >> 3, fl = imin(f, 7 - f), cr = imin(r, 7 - r), cen = fl + cr;
    int mg[6], eg[6];
    mg[PAWN] = MGP[r] + (r >= 2 ? (fl - 1) * 4 - 2 : 0); eg[PAWN] = EGP[r];
    mg[KNIGHT] = (cen >= 3 ? (cen - 3) * 12 : (cen - 3) * 18) + (r > 0 ? 0 : -8); eg[KNIGHT] = cen >= 3 ? (cen - 3) * 9 : (cen - 3) * 14;
    int dg = (f == r || f + r == 7) ? 1 : 0;
    mg[BISHOP] = (cen - 3) * 6 + dg * 6; eg[BISHOP] = (cen - 3) * 5 + dg * 4;
    mg[ROOK] = (fl >= 2 ? 4 : 0) + (fl == 3 ? 2 : 0); eg[ROOK] = 0;
    mg[QUEEN] = (cen - 3) * 3; eg[QUEEN] = (cen - 3) * 7;
    mg[KING] = r == 0 ? KBACK[f] : -r * 28 - 10; eg[KING] = (cen - 2) * 16;
    for(int t = 0; t < 6; t++){
      PSQ_MG[t][sq] = MGV[t] + mg[t]; PSQ_EG[t][sq] = EGV[t] + eg[t];
      PSQ_MG[6 + t][sq ^ 56] = MGV[t] + mg[t]; PSQ_EG[6 + t][sq ^ 56] = EGV[t] + eg[t]; } } }

static void px_init_impl(){
  if(inited) return; inited = true;
  for(int s = 0; s < 64; s++){
    int r = s >> 3, f = s & 7; PATT[0][s] = PATT[1][s] = NATT[s] = KATT[s] = 0;
    for(int dr = -1; dr <= 1; dr++) for(int df = -1; df <= 1; df++){ if(!dr && !df) continue; int rr = r + dr, ff = f + df;
      if(rr >= 0 && rr < 8 && ff >= 0 && ff < 8) KATT[s] |= 1ULL << (rr * 8 + ff); }
    static const int nr[8] = {1,2,2,1,-1,-2,-2,-1}, nf[8] = {2,1,-1,-2,-2,-1,1,2};
    for(int i = 0; i < 8; i++){ int rr = r + nr[i], ff = f + nf[i]; if(rr >= 0 && rr < 8 && ff >= 0 && ff < 8) NATT[s] |= 1ULL << (rr * 8 + ff); }
    if(r < 7){ if(f > 0) PATT[0][s] |= 1ULL << (s + 7); if(f < 7) PATT[0][s] |= 1ULL << (s + 9); }
    if(r > 0){ if(f > 0) PATT[1][s] |= 1ULL << (s - 9); if(f < 7) PATT[1][s] |= 1ULL << (s - 7); } }
  for(int f = 0; f < 8; f++){ FILEBB[f] = FILE_A << f; ADJF[f] = (f > 0 ? FILE_A << (f - 1) : 0) | (f < 7 ? FILE_A << (f + 1) : 0); }
  for(int s = 0; s < 64; s++){ int r = s >> 3, f = s & 7;
    U64 w = 0, b = 0, wo = 0, bo = 0;
    for(int rr = 0; rr < 8; rr++) for(int ff = imax(0, f - 1); ff <= imin(7, f + 1); ff++){ U64 bit = 1ULL << (rr * 8 + ff);
      if(rr > r){ w |= bit; if(ff != f) wo |= bit; } if(rr < r){ b |= bit; if(ff != f) bo |= bit; } }
    PASSM[0][s] = w; PASSM[1][s] = b; OUTP[0][s] = wo; OUTP[1][s] = bo; }
  for(int i = 0; i < 64; i++) CMASK[i] = 15;
  CMASK[4] &= ~3; CMASK[0] &= ~2; CMASK[7] &= ~1; CMASK[60] &= ~12; CMASK[56] &= ~8; CMASK[63] &= ~4;
  rngS = 0x1234567ULL * 0x9E3779B97F4A7C15ULL + 99;
  for(int p = 0; p < 12; p++) for(int s = 0; s < 64; s++) ZOB[p][s] = rnd64();
  for(int i = 0; i < 16; i++) ZCAST[i] = rnd64(); for(int i = 0; i < 8; i++) ZEP[i] = rnd64(); ZSIDE = rnd64();
  initMagics(true); initMagics(false); initPST();
  for(int d = 0; d < 64; d++) for(int m = 0; m < 64; m++) LMRT[d][m] = (d < 1 || m < 1) ? 0 : (int)(0.75 + pxlog((double)d) * pxlog((double)m) / 2.25); }

/* ---- position ---- */
struct Pos { U64 bb[12], occ[2], all; U8 mb[64]; int stm, castle, ep, half; U64 key, pkey; };
struct Undo { U64 key, pkey; int castle, ep, half; U8 cap; };
static Pos P; static Undo UN[MAXPLY + 8];
static U64 KEYS[MAXPLY + 256]; static int rootIdx = 0;

static inline void putPc(int pc, int sq){ U64 b = 1ULL << sq; P.bb[pc] |= b; P.occ[pc >= 6] |= b; P.all |= b; P.mb[sq] = (U8)pc; }
static inline void delPc(int pc, int sq){ U64 b = ~(1ULL << sq); P.bb[pc] &= b; P.occ[pc >= 6] &= b; P.all &= b; P.mb[sq] = NOPC; }

static void hashPos(Pos& p){
  p.key = p.pkey = 0;
  for(int s = 0; s < 64; s++){ int pc = p.mb[s]; if(pc == NOPC) continue; p.key ^= ZOB[pc][s]; if(pc % 6 == PAWN) p.pkey ^= ZOB[pc][s]; }
  p.key ^= ZCAST[p.castle]; if(p.ep >= 0) p.key ^= ZEP[p.ep & 7]; if(p.stm) p.key ^= ZSIDE; }

static void setupIO(const int* a, Pos& p){
  for(int i = 0; i < 12; i++) p.bb[i] = 0; p.occ[0] = p.occ[1] = p.all = 0; for(int i = 0; i < 64; i++) p.mb[i] = NOPC;
  Pos save = P; P = p;                                    /* putPc works on the global P */
  for(int i = 0; i < 64; i++){ int c = a[i]; if(!c) continue; int t = (c & 7) - 1, col = (c >> 3) & 1; if(t < 0 || t > 5) continue; putPc(col * 6 + t, i ^ 56); }
  P.stm = a[64] & 1; P.castle = a[65] & 15; P.ep = -1; P.half = 0;
  if(P.mb[4] != 5) P.castle &= ~3; if(P.mb[7] != 3) P.castle &= ~1; if(P.mb[0] != 3) P.castle &= ~2;
  if(P.mb[60] != 11) P.castle &= ~12; if(P.mb[63] != 9) P.castle &= ~4; if(P.mb[56] != 9) P.castle &= ~8;
  int e = a[66]; if(e >= 0 && e < 64){ int sq = e ^ 56; if((sq >> 3) == (P.stm == WHITE ? 5 : 2) && (PATT[P.stm ^ 1][sq] & P.bb[P.stm * 6 + PAWN])) P.ep = sq; }
  hashPos(P); p = P; P = save; }

static inline U64 attacksTo(int s, U64 occ){
  return (PATT[1][s] & P.bb[PAWN]) | (PATT[0][s] & P.bb[6 + PAWN]) | (NATT[s] & (P.bb[KNIGHT] | P.bb[6 + KNIGHT])) | (KATT[s] & (P.bb[KING] | P.bb[6 + KING]))
       | (bishopAtt(s, occ) & (P.bb[BISHOP] | P.bb[6 + BISHOP] | P.bb[QUEEN] | P.bb[6 + QUEEN]))
       | (rookAtt(s, occ) & (P.bb[ROOK] | P.bb[6 + ROOK] | P.bb[QUEEN] | P.bb[6 + QUEEN])); }
static inline bool attackedBy(int s, int by, U64 occ){
  const U64* b = P.bb + by * 6;
  return (PATT[by ^ 1][s] & b[PAWN]) || (NATT[s] & b[KNIGHT]) || (KATT[s] & b[KING]) || (bishopAtt(s, occ) & (b[BISHOP] | b[QUEEN])) || (rookAtt(s, occ) & (b[ROOK] | b[QUEEN])); }
static inline bool inCheckNow(){ return attackedBy(lsb(P.bb[P.stm * 6 + KING]), P.stm ^ 1, P.all); }

/* move: from | to<<6 | flag<<12 ; flag: 0 quiet, 1 double push, 2 O-O, 3 O-O-O, 4 capture, 5 ep, 8+k promo, 12+k promo capture (k: N B R Q) */
static inline void addm(U16* mv, int& n, int f, int t, int fl){ mv[n++] = (U16)(f | (t << 6) | (fl << 12)); }
static int genMoves(U16* mv, bool caps){
  int n = 0; const int us = P.stm, them = us ^ 1; const U64 all = P.all, own = P.occ[us], opp = P.occ[them], pw = P.bb[us * 6 + PAWN], empty = ~all;
  U64 one, two, c1, c2, b; int to;
  if(us == WHITE){
    one = (pw << 8) & empty; two = ((one & RANK_3) << 8) & empty;
    b = one & RANK_8; while(b){ to = poplsb(b); if(caps) addm(mv, n, to - 8, to, 11); else { addm(mv, n, to - 8, to, 11); addm(mv, n, to - 8, to, 10); addm(mv, n, to - 8, to, 9); addm(mv, n, to - 8, to, 8); } }
    if(!caps){ b = one & ~RANK_8; while(b){ to = poplsb(b); addm(mv, n, to - 8, to, 0); } b = two; while(b){ to = poplsb(b); addm(mv, n, to - 16, to, 1); } }
    c1 = ((pw & ~FILE_A) << 7) & opp; c2 = ((pw & ~FILE_H) << 9) & opp;
    b = c1; while(b){ to = poplsb(b); if(to >= 56){ addm(mv, n, to - 7, to, 15); if(!caps){ addm(mv, n, to - 7, to, 14); addm(mv, n, to - 7, to, 13); addm(mv, n, to - 7, to, 12); } } else addm(mv, n, to - 7, to, 4); }
    b = c2; while(b){ to = poplsb(b); if(to >= 56){ addm(mv, n, to - 9, to, 15); if(!caps){ addm(mv, n, to - 9, to, 14); addm(mv, n, to - 9, to, 13); addm(mv, n, to - 9, to, 12); } } else addm(mv, n, to - 9, to, 4); }
  } else {
    one = (pw >> 8) & empty; two = ((one & RANK_6) >> 8) & empty;
    b = one & RANK_1; while(b){ to = poplsb(b); if(caps) addm(mv, n, to + 8, to, 11); else { addm(mv, n, to + 8, to, 11); addm(mv, n, to + 8, to, 10); addm(mv, n, to + 8, to, 9); addm(mv, n, to + 8, to, 8); } }
    if(!caps){ b = one & ~RANK_1; while(b){ to = poplsb(b); addm(mv, n, to + 8, to, 0); } b = two; while(b){ to = poplsb(b); addm(mv, n, to + 16, to, 1); } }
    c1 = ((pw & ~FILE_A) >> 9) & opp; c2 = ((pw & ~FILE_H) >> 7) & opp;
    b = c1; while(b){ to = poplsb(b); if(to < 8){ addm(mv, n, to + 9, to, 15); if(!caps){ addm(mv, n, to + 9, to, 14); addm(mv, n, to + 9, to, 13); addm(mv, n, to + 9, to, 12); } } else addm(mv, n, to + 9, to, 4); }
    b = c2; while(b){ to = poplsb(b); if(to < 8){ addm(mv, n, to + 7, to, 15); if(!caps){ addm(mv, n, to + 7, to, 14); addm(mv, n, to + 7, to, 13); addm(mv, n, to + 7, to, 12); } } else addm(mv, n, to + 7, to, 4); } }
  if(P.ep >= 0){ b = PATT[them][P.ep] & pw; while(b){ int f = poplsb(b); addm(mv, n, f, P.ep, 5); } }
  const U64 tg = caps ? opp : ~own;
  for(int t = KNIGHT; t <= QUEEN; t++){ U64 bs = P.bb[us * 6 + t];
    while(bs){ int f = poplsb(bs); U64 a = t == KNIGHT ? NATT[f] : t == BISHOP ? bishopAtt(f, all) : t == ROOK ? rookAtt(f, all) : (bishopAtt(f, all) | rookAtt(f, all));
      a &= tg; while(a){ to = poplsb(a); addm(mv, n, f, to, (opp >> to) & 1 ? 4 : 0); } } }
  { int f = lsb(P.bb[us * 6 + KING]); U64 a = KATT[f] & tg; while(a){ to = poplsb(a); addm(mv, n, f, to, (opp >> to) & 1 ? 4 : 0); }
    if(!caps){
      if(us == WHITE){
        if((P.castle & 1) && !(all & 0x60ULL) && !attackedBy(4, BLACK, all) && !attackedBy(5, BLACK, all)) addm(mv, n, 4, 6, 2);
        if((P.castle & 2) && !(all & 0x0EULL) && !attackedBy(4, BLACK, all) && !attackedBy(3, BLACK, all)) addm(mv, n, 4, 2, 3);
      } else {
        if((P.castle & 4) && !(all & (0x60ULL << 56)) && !attackedBy(60, WHITE, all) && !attackedBy(61, WHITE, all)) addm(mv, n, 60, 62, 2);
        if((P.castle & 8) && !(all & (0x0EULL << 56)) && !attackedBy(60, WHITE, all) && !attackedBy(59, WHITE, all)) addm(mv, n, 60, 58, 3); } } }
  return n; }

static void doMove(U16 m, Undo& u){
  const int from = m & 63, to = (m >> 6) & 63, fl = m >> 12, us = P.stm, them = us ^ 1, pc = P.mb[from];
  u.key = P.key; u.pkey = P.pkey; u.castle = P.castle; u.ep = P.ep; u.half = P.half; u.cap = NOPC;
  P.key ^= ZCAST[P.castle]; if(P.ep >= 0) P.key ^= ZEP[P.ep & 7]; P.ep = -1; P.half++;
  if(fl & 4){ int cs = fl == 5 ? (us == WHITE ? to - 8 : to + 8) : to; int cp = P.mb[cs]; u.cap = (U8)cp; delPc(cp, cs); P.key ^= ZOB[cp][cs]; if(cp % 6 == PAWN) P.pkey ^= ZOB[cp][cs]; P.half = 0; }
  delPc(pc, from); P.key ^= ZOB[pc][from];
  int npc = pc; if(fl & 8) npc = us * 6 + (fl & 3) + 1;
  putPc(npc, to); P.key ^= ZOB[npc][to];
  if(pc % 6 == PAWN){ P.half = 0; P.pkey ^= ZOB[pc][from]; if(!(fl & 8)) P.pkey ^= ZOB[pc][to];
    if(fl == 1){ int es = (from + to) / 2; if(PATT[us][es] & P.bb[them * 6 + PAWN]){ P.ep = es; P.key ^= ZEP[es & 7]; } } }
  if(fl == 2 || fl == 3){ int rf = fl == 2 ? (us == WHITE ? 7 : 63) : (us == WHITE ? 0 : 56), rt = fl == 2 ? rf - 2 : rf + 3, rp = us * 6 + ROOK;
    delPc(rp, rf); putPc(rp, rt); P.key ^= ZOB[rp][rf] ^ ZOB[rp][rt]; }
  P.castle &= CMASK[from] & CMASK[to]; P.key ^= ZCAST[P.castle]; P.stm = them; P.key ^= ZSIDE; }

static void undoMove(U16 m, const Undo& u){
  P.stm ^= 1; const int us = P.stm, from = m & 63, to = (m >> 6) & 63, fl = m >> 12;
  int pc = (fl & 8) ? us * 6 + PAWN : P.mb[to];
  delPc(P.mb[to], to); putPc(pc, from);
  if(fl == 2 || fl == 3){ int rf = fl == 2 ? (us == WHITE ? 7 : 63) : (us == WHITE ? 0 : 56), rt = fl == 2 ? rf - 2 : rf + 3, rp = us * 6 + ROOK; delPc(rp, rt); putPc(rp, rf); }
  if(u.cap != NOPC){ int cs = fl == 5 ? (us == WHITE ? to - 8 : to + 8) : to; putPc(u.cap, cs); }
  P.key = u.key; P.pkey = u.pkey; P.castle = u.castle; P.ep = u.ep; P.half = u.half; }
static void doNull(Undo& u){ u.key = P.key; u.ep = P.ep; u.half = P.half; if(P.ep >= 0) P.key ^= ZEP[P.ep & 7]; P.ep = -1; P.half++; P.stm ^= 1; P.key ^= ZSIDE; }
static void undoNull(const Undo& u){ P.stm ^= 1; P.key = u.key; P.ep = u.ep; P.half = u.half; }

static bool seeGE(U16 m, int th){
  const int from = m & 63, to = (m >> 6) & 63, fl = m >> 12;
  int victim = fl == 5 ? PAWN : (P.mb[to] == NOPC ? -1 : P.mb[to] % 6);
  int sw = (victim < 0 ? 0 : PVAL[victim]) - th; if(sw < 0) return false;
  sw = PVAL[P.mb[from] % 6] - sw; if(sw <= 0) return true;
  U64 occ = P.all ^ (1ULL << from) ^ (1ULL << to); int stm = P.stm; U64 att = attacksTo(to, occ); int res = 1;
  const U64 bq = P.bb[BISHOP] | P.bb[6 + BISHOP] | P.bb[QUEEN] | P.bb[6 + QUEEN], rq = P.bb[ROOK] | P.bb[6 + ROOK] | P.bb[QUEEN] | P.bb[6 + QUEEN];
  for(;;){
    stm ^= 1; att &= occ; U64 sa = att & P.occ[stm]; if(!sa) break; res ^= 1; U64 b;
    if((b = sa & P.bb[stm * 6 + PAWN])){ sw = PVAL[PAWN] - sw; if(sw < res) break; occ ^= b & -b; att |= bishopAtt(to, occ) & bq; }
    else if((b = sa & P.bb[stm * 6 + KNIGHT])){ sw = PVAL[KNIGHT] - sw; if(sw < res) break; occ ^= b & -b; }
    else if((b = sa & P.bb[stm * 6 + BISHOP])){ sw = PVAL[BISHOP] - sw; if(sw < res) break; occ ^= b & -b; att |= bishopAtt(to, occ) & bq; }
    else if((b = sa & P.bb[stm * 6 + ROOK])){ sw = PVAL[ROOK] - sw; if(sw < res) break; occ ^= b & -b; att |= rookAtt(to, occ) & rq; }
    else if((b = sa & P.bb[stm * 6 + QUEEN])){ sw = PVAL[QUEEN] - sw; if(sw < res) break; occ ^= b & -b; att |= (bishopAtt(to, occ) & bq) | (rookAtt(to, occ) & rq); }
    else return (att & ~P.occ[stm]) ? (res ^ 1) : res; }
  return res; }

static bool insufficient(){
  if(P.bb[PAWN] | P.bb[6 + PAWN] | P.bb[ROOK] | P.bb[6 + ROOK] | P.bb[QUEEN] | P.bb[6 + QUEEN]) return false;
  return popc(P.bb[KNIGHT] | P.bb[6 + KNIGHT] | P.bb[BISHOP] | P.bb[6 + BISHOP]) <= 1; }

/* ---- evaluation ---- */
struct PawnEnt { U64 key; int mg[2], eg[2]; U64 passed[2]; };
static PawnEnt PTAB[1 << 13];
static inline int cheb(int a, int b){ return imax(iabs((a >> 3) - (b >> 3)), iabs((a & 7) - (b & 7))); }
static inline int cmd(int s){ return (3 - imin(s & 7, 7 - (s & 7))) + (3 - imin(s >> 3, 7 - (s >> 3))); }

static PawnEnt* pawnEval(){
  PawnEnt* e = &PTAB[P.pkey & ((1 << 13) - 1)]; if(e->key == P.pkey) return e;
  e->key = P.pkey;
  static const int CONN[8] = { 0, 0, 6, 8, 14, 26, 50, 0 };
  for(int c = 0; c < 2; c++){
    const int them = c ^ 1; const U64 mine = P.bb[c * 6 + PAWN], theirs = P.bb[them * 6 + PAWN]; int mg = 0, eg = 0; U64 pas = 0, b = mine;
    while(b){ int s = poplsb(b); int f = s & 7, rr = c == WHITE ? (s >> 3) : 7 - (s >> 3);
      mg += PSQ_MG[c * 6 + PAWN][s]; eg += PSQ_EG[c * 6 + PAWN][s];
      U64 ahead = c == WHITE ? (FILEBB[f] & ~((2ULL << s) - 1)) : (FILEBB[f] & ((1ULL << s) - 1));
      bool doubled = (mine & ahead) != 0, iso = !(mine & ADJF[f]), passed = !(theirs & PASSM[c][s]) && !doubled;
      bool supp = (PATT[them][s] & mine) != 0, phal = (mine & ADJF[f] & (0xFFULL << ((s >> 3) * 8))) != 0;
      if(doubled){ mg -= 10; eg -= 20; }
      if(iso){ mg -= 10; eg -= 14; }
      else if(!supp && !phal && !(mine & ADJF[f] & PASSM[them][s])){ int stop = c == WHITE ? s + 8 : s - 8; if(PATT[c][stop] & theirs){ mg -= 9; eg -= 12; } }
      if(supp || phal){ mg += CONN[rr]; eg += CONN[rr] * 3 / 2; }
      if(passed) pas |= 1ULL << s; }
    e->mg[c] = mg; e->eg[c] = eg; e->passed[c] = pas; }
  return e; }

static int evaluate(){
  if(insufficient()) return 0;
  const int us0 = P.stm; int mg[2], eg[2], phase = 0;
  PawnEnt* pe = pawnEval(); mg[0] = pe->mg[0]; mg[1] = pe->mg[1]; eg[0] = pe->eg[0]; eg[1] = pe->eg[1];
  const U64 pw[2] = { P.bb[PAWN], P.bb[6 + PAWN] };
  const U64 pa[2] = { ((pw[0] & ~FILE_A) << 7) | ((pw[0] & ~FILE_H) << 9), ((pw[1] & ~FILE_A) >> 9) | ((pw[1] & ~FILE_H) >> 7) };
  const int ksq[2] = { lsb(P.bb[KING]), lsb(P.bb[6 + KING]) };
  U64 attAll[2] = { pa[0] | KATT[ksq[0]], pa[1] | KATT[ksq[1]] }, minorAtt[2] = { 0, 0 };
  U64 zone[2]; { U64 z0 = KATT[ksq[0]] | (1ULL << ksq[0]), z1 = KATT[ksq[1]] | (1ULL << ksq[1]); zone[0] = z0 | (z0 << 8); zone[1] = z1 | (z1 >> 8); }
  int kaCnt[2] = { 0, 0 }, kaUnits[2] = { 0, 0 }, npm[2] = { 0, 0 };
  static const int KAW[6] = { 0, 3, 3, 4, 6, 0 };
  for(int c = 0; c < 2; c++){
    const int them = c ^ 1; const U64 mobArea = ~(P.bb[c * 6 + PAWN] | P.bb[c * 6 + KING]) & ~pa[them];
    for(int t = KNIGHT; t <= QUEEN; t++){ U64 bs = P.bb[c * 6 + t];
      while(bs){ int s = poplsb(bs); int f = s & 7, rr = c == WHITE ? (s >> 3) : 7 - (s >> 3);
        U64 a = t == KNIGHT ? NATT[s] : t == BISHOP ? bishopAtt(s, P.all) : t == ROOK ? rookAtt(s, P.all) : (bishopAtt(s, P.all) | rookAtt(s, P.all));
        int mob = popc(a & mobArea); attAll[c] |= a; npm[c] += PVAL[t];
        mg[c] += PSQ_MG[c * 6 + t][s]; eg[c] += PSQ_EG[c * 6 + t][s];
        if(a & zone[them]){ kaCnt[c]++; kaUnits[c] += KAW[t] * popc(a & zone[them]); }
        switch(t){
          case KNIGHT: phase += 1; minorAtt[c] |= a; mg[c] += (mob - 4) * 4; eg[c] += (mob - 4) * 4;
            if(rr >= 3 && rr <= 5 && (PATT[them][s] & P.bb[c * 6 + PAWN]) && !(OUTP[c][s] & pw[them])){ mg[c] += 22; eg[c] += 10; } break;
          case BISHOP: phase += 1; minorAtt[c] |= a; mg[c] += (mob - 6) * 5; eg[c] += (mob - 6) * 5; break;
          case ROOK: phase += 2; mg[c] += (mob - 6) * 2; eg[c] += (mob - 6) * 4;
            if(!(pw[c] & FILEBB[f])){ if(!(pw[them] & FILEBB[f])){ mg[c] += 24; eg[c] += 12; } else { mg[c] += 12; eg[c] += 10; } }
            if(rr == 6 && ((P.bb[them * 6 + KING] & (c == WHITE ? RANK_8 : RANK_1)) || (pw[them] & (c == WHITE ? RANK_8 >> 8 : RANK_1 << 8)))){ mg[c] += 20; eg[c] += 30; } break;
          default: phase += 4; mg[c] += (mob - 12); eg[c] += (mob - 12) * 2; } } }
    if(popc(P.bb[c * 6 + BISHOP]) >= 2){ mg[c] += 30; eg[c] += 50; }
    mg[c] += PSQ_MG[c * 6 + KING][ksq[c]]; eg[c] += PSQ_EG[c * 6 + KING][ksq[c]]; }
  for(int c = 0; c < 2; c++){
    const int them = c ^ 1; const int ks = ksq[c]; const int kr = ks >> 3, kf = ks & 7;
    /* pawn shield (middlegame only) */
    int sh = 0; static const int SH[8] = { 14, 14, 8, 2, 0, 0, 0, 0 };
    for(int ff = imax(0, kf - 1); ff <= imin(7, kf + 1); ff++){
      U64 fp = pw[c] & FILEBB[ff]; fp &= c == WHITE ? ~((1ULL << (kr * 8)) - 1) : (kr == 7 ? ~0ULL : (1ULL << ((kr + 1) * 8)) - 1);
      if(!fp) sh -= ff == kf ? 28 : 20; else { int pr = c == WHITE ? lsb(fp) >> 3 : msb(fp) >> 3; sh += SH[iabs(pr - kr)]; } }
    mg[c] += sh;
    /* king danger from the enemy attackers */
    if(kaCnt[them] >= 2 || (kaCnt[them] >= 1 && P.bb[them * 6 + QUEEN])){ int u = kaUnits[them], pen = imin(u * u / 9, 600); if(!P.bb[them * 6 + QUEEN]) pen /= 2; mg[c] -= pen; eg[c] -= pen / 8; }
    /* threats */
    const U64 np = P.occ[them] & ~pw[them] & ~P.bb[them * 6 + KING];
    int tp = popc(pa[c] & np); mg[c] += tp * 30; eg[c] += tp * 20;
    int th = popc(np & attAll[c] & ~attAll[them]); mg[c] += th * 14; eg[c] += th * 10;
    int tm = popc(minorAtt[c] & (P.bb[them * 6 + ROOK] | P.bb[them * 6 + QUEEN])); mg[c] += tm * 20; eg[c] += tm * 12;
    /* passed pawns */
    U64 ps = pe->passed[c];
    while(ps){ int s = poplsb(ps); int rr = c == WHITE ? (s >> 3) : 7 - (s >> 3); int stop = c == WHITE ? s + 8 : s - 8;
      static const int PM[8] = { 0, 2, 5, 12, 30, 60, 110, 0 }, PE[8] = { 0, 5, 12, 28, 55, 100, 170, 0 };
      int bm = PM[rr], be = PE[rr];
      if(P.all & (1ULL << stop)){ bm = bm * 6 / 10; be = be * 6 / 10; }
      if(rr >= 3) be += (imin(cheb(ksq[them], stop), 5) * 5 - imin(cheb(ksq[c], stop), 5) * 3) * (rr - 2);
      if(!(npm[them]) ){ int prom = c == WHITE ? (s & 7) + 56 : (s & 7); int pd = 7 - rr - (rr == 1 ? 1 : 0);
        if(cheb(ksq[them], prom) - (us0 == them ? 1 : 0) > pd) be += 350 + rr * 10; }
      mg[c] += bm; eg[c] += be; } }
  int m = mg[0] - mg[1], e = eg[0] - eg[1];
  /* mop-up: drive the lone king to the corner when ahead in material */
  for(int w = 0; w < 2; w++){ int l = w ^ 1; if(!pw[l] && npm[l] <= 350 && npm[w] >= npm[l] + 450){ int v = 12 * cmd(ksq[l]) + 6 * (14 - (iabs((ksq[0] >> 3) - (ksq[1] >> 3)) + iabs((ksq[0] & 7) - (ksq[1] & 7)))); e += w == 0 ? v : -v; } }
  int ph = imin(phase, 24); int sc = (m * ph + e * (24 - ph)) / 24;
  { int w = sc > 0 ? 0 : 1, l = w ^ 1;
    if(!pw[w] && npm[w] - npm[l] <= 350 && npm[l] + npm[w] > 0) sc /= 8;
    else if(popc(P.bb[BISHOP]) == 1 && popc(P.bb[6 + BISHOP]) == 1 && npm[0] == 330 && npm[1] == 330){
      bool wl = (lsb(P.bb[BISHOP]) + (lsb(P.bb[BISHOP]) >> 3)) & 1, bl = (lsb(P.bb[6 + BISHOP]) + (lsb(P.bb[6 + BISHOP]) >> 3)) & 1; if(wl != bl) sc /= 2; } }
  if(P.half > 20) sc = sc * (200 - P.half) / 200;
  return (us0 == WHITE ? sc : -sc) + 12; }

/* ---- transposition table ---- */
struct TTE { U32 k; U16 mv; I16 sc; I16 ev; U8 d; U8 fa; };
#define TTN (1ULL << PX_TT_BITS)
static TTE TT[TTN]; static int ttGen = 0;
enum { B_NONE = 0, B_LOW = 1, B_UP = 2, B_EXACT = 3 };
static inline int toTT(int s, int ply){ return s >= MATE_BOUND ? s + ply : s <= -MATE_BOUND ? s - ply : s; }
static inline int fromTT(int s, int ply){ return s >= MATE_BOUND ? s - ply : s <= -MATE_BOUND ? s + ply : s; }
static inline TTE* ttProbe(U64 key, bool& hit){
  TTE* b = &TT[(key & (TTN - 1)) & ~1ULL]; U32 k = (U32)(key >> 32);
  if(b[0].k == k && (b[0].fa & 3)){ hit = true; return &b[0]; } if(b[1].k == k && (b[1].fa & 3)){ hit = true; return &b[1]; }
  hit = false; int a0 = b[0].d - 4 * ((ttGen - (b[0].fa >> 2)) & 63), a1 = b[1].d - 4 * ((ttGen - (b[1].fa >> 2)) & 63);
  if(!(b[0].fa & 3)) return &b[0]; if(!(b[1].fa & 3)) return &b[1]; return a0 <= a1 ? &b[0] : &b[1]; }
static inline void ttStore(TTE* e, bool hit, U64 key, int d, int bound, int sc, int ev, U16 mv, int ply){
  U32 k = (U32)(key >> 32);
  if(hit && !mv) mv = e->mv;
  if(hit && bound != B_EXACT && d + 3 < e->d && (e->fa >> 2) == (ttGen & 63)) { if(!e->mv) e->mv = mv; return; }
  e->k = k; e->mv = mv; e->sc = (I16)toTT(sc, ply); e->ev = (I16)ev; e->d = (U8)(d < 0 ? 0 : d); e->fa = (U8)(((ttGen & 63) << 2) | bound); }

/* ---- search state ---- */
struct SStack { int eval; U16 k1, k2; U16 mv; U8 pc, to; };
static SStack SS[MAXPLY + 8];
static int HIST[2][64][64]; static U16 COUNTER[12][64];
static U64 nodes; static double t0, hardMs; static bool stopFlag; static int rootDepth; static U16 rootBestIter;
static bool weak; static int qMax;

static inline void checkTime(){ if(hardMs > 0 && rootDepth > 1 && px_now() - t0 >= hardMs) stopFlag = true; }
static inline void histUpd(int& h, int bonus){ h += bonus - h * iabs(bonus) / 16384; }
struct ML { U16 m[256]; int s[256]; int n; };

static bool isDraw(int ply){
  if(P.half >= 100) return true;
  if(insufficient()) return true;
  int idx = rootIdx + ply; for(int i = idx - 2; i >= 0 && i >= idx - P.half; i -= 2) if(KEYS[i] == P.key) return true;
  return false; }

static void scoreMoves(ML& l, U16 ttm, int ply){
  const int us = P.stm; const U16 k1 = SS[ply].k1, k2 = SS[ply].k2;
  U16 cm = 0; if(ply > 0 && SS[ply - 1].mv) cm = COUNTER[SS[ply - 1].pc][SS[ply - 1].to];
  for(int i = 0; i < l.n; i++){ U16 m = l.m[i]; int from = m & 63, to = (m >> 6) & 63, fl = m >> 12;
    if(m == ttm){ l.s[i] = 1 << 28; continue; }
    if((fl & 4) || (fl & 8)){ int victim = fl == 5 ? PAWN : (P.mb[to] == NOPC ? -1 : P.mb[to] % 6); int att = P.mb[from] % 6;
      int mvv = (victim < 0 ? 0 : PVAL[victim]) * 16 - att + ((fl & 8) ? ((fl & 3) == 3 ? 8000 : -8000) : 0);
      bool good = (victim >= 0 && PVAL[victim] >= PVAL[att]) || seeGE(m, 0);
      l.s[i] = good ? (1 << 26) + mvv : -(1 << 20) + mvv; }
    else if(m == k1) l.s[i] = 1 << 25; else if(m == k2) l.s[i] = (1 << 25) - 1; else if(m == cm) l.s[i] = 1 << 24;
    else l.s[i] = HIST[us][from][to]; } }
static inline void pickBest(ML& l, int i){ int b = i; for(int j = i + 1; j < l.n; j++) if(l.s[j] > l.s[b]) b = j;
  if(b != i){ U16 tm = l.m[i]; l.m[i] = l.m[b]; l.m[b] = tm; int ts = l.s[i]; l.s[i] = l.s[b]; l.s[b] = ts; } }

static int qsearch(int alpha, int beta, int ply, int qd){
  nodes++; if((nodes & 1023) == 0) checkTime(); if(stopFlag) return 0;
  KEYS[rootIdx + ply] = P.key;
  const bool pv = beta - alpha > 1; const bool inChk = inCheckNow();
  if(ply >= MAXPLY - 1) return inChk ? 0 : evaluate();
  if(insufficient()) return 0;
  int stand = -INFV, best = -INFV; const int origAlpha = alpha;
  bool hit; TTE* te = ttProbe(P.key, hit); U16 ttm = hit ? te->mv : 0;
  if(hit && !pv){ int ts = fromTT(te->sc, ply), bd = te->fa & 3; if(bd == B_EXACT || (bd == B_LOW && ts >= beta) || (bd == B_UP && ts <= alpha)) return ts; }
  if(!inChk){ stand = hit ? te->ev : evaluate(); if(!hit || te->ev == 0) stand = evaluate(); if(stand >= beta) return stand; if(qd >= qMax) return stand; if(stand > alpha) alpha = stand; best = stand; }
  ML l; l.n = genMoves(l.m, !inChk); scoreMoves(l, ttm, ply);
  int moves = 0; U16 bestMove = 0;
  for(int i = 0; i < l.n; i++){ pickBest(l, i); U16 m = l.m[i]; int fl = m >> 12;
    if(!inChk){ if(l.s[i] < 0 && !(fl & 8)) continue;
      int to = (m >> 6) & 63; int victim = fl == 5 ? PAWN : (P.mb[to] == NOPC ? -1 : P.mb[to] % 6);
      if(!(fl & 8) && stand + (victim < 0 ? 0 : PVAL[victim]) + 200 < alpha) continue; }
    doMove(m, UN[ply]);
    if(attackedBy(lsb(P.bb[(P.stm ^ 1) * 6 + KING]), P.stm, P.all)){ undoMove(m, UN[ply]); continue; }
    moves++; SS[ply].mv = m; SS[ply].pc = P.mb[(m >> 6) & 63]; SS[ply].to = (m >> 6) & 63;
    int v = -qsearch(-beta, -alpha, ply + 1, qd + 1); undoMove(m, UN[ply]); if(stopFlag) return 0;
    if(v > best){ best = v; bestMove = m; if(v > alpha){ alpha = v; if(v >= beta) break; } } }
  if(inChk && moves == 0) return -MATE + ply;
  ttStore(te, hit, P.key, 0, best >= beta ? B_LOW : (best > origAlpha ? B_EXACT : B_UP), best, inChk ? 0 : stand, bestMove, ply);
  return best; }

static int search(int depth, int alpha, int beta, int ply, bool nullOk, U16 excl){
  const bool pv = beta - alpha > 1; const bool root = ply == 0; const int us = P.stm;
  KEYS[rootIdx + ply] = P.key;
  const bool inChk = inCheckNow();
  if(ply >= MAXPLY - 2) return inChk ? 0 : evaluate();
  if(!root){ if(isDraw(ply)) return 0; alpha = imax(alpha, -MATE + ply); beta = imin(beta, MATE - ply - 1); if(alpha >= beta) return alpha; }
  if(inChk) depth++;
  if(depth <= 0) return qsearch(alpha, beta, ply, 0);
  nodes++; if((nodes & 1023) == 0) checkTime(); if(stopFlag) return 0;
  SS[ply + 1].k1 = SS[ply + 1].k2 = 0; SS[ply + 2].k1 = SS[ply + 2].k2 = 0;
  bool hit; TTE* te = ttProbe(P.key, hit); U16 ttm = hit ? te->mv : 0; int ttScore = hit ? fromTT(te->sc, ply) : 0; int ttBound = hit ? (te->fa & 3) : 0;
  if(!pv && hit && !excl && te->d >= depth && P.half < 90){
    if(ttBound == B_EXACT || (ttBound == B_LOW && ttScore >= beta) || (ttBound == B_UP && ttScore <= alpha)) return ttScore; }
  int ev = -INFV; bool improving = false;
  if(!inChk){ ev = (hit && te->ev) ? te->ev : evaluate(); SS[ply].eval = ev;
    if(hit && ((ttBound == B_LOW && ttScore > ev) || (ttBound == B_UP && ttScore < ev) || ttBound == B_EXACT)) ev = ttScore;
    improving = ply >= 2 && SS[ply - 2].eval != -INFV && SS[ply].eval > SS[ply - 2].eval; } else SS[ply].eval = -INFV;
  if(!weak && !pv && !inChk && !excl && iabs(beta) < MATE_BOUND){
    if(depth <= 7 && ev - 85 * (depth - (improving ? 1 : 0)) >= beta) return ev;
    if(depth <= 2 && ev + 300 < alpha){ int v = qsearch(alpha, alpha + 1, ply, 0); if(v <= alpha) return v; }
    if(nullOk && depth >= 3 && ev >= beta && (P.occ[us] & ~(P.bb[us * 6 + PAWN] | P.bb[us * 6 + KING]))){
      int R = 3 + depth / 4 + imin((ev - beta) / 200, 3); doNull(UN[ply]); SS[ply].mv = 0;
      int v = -search(depth - R, -beta, -beta + 1, ply + 1, false, 0); undoNull(UN[ply]); if(stopFlag) return 0;
      if(v >= beta) return v >= MATE_BOUND ? beta : v; } }
  if(!weak && depth >= 4 && !ttm && !excl) depth--;
  ML l; l.n = genMoves(l.m, false); scoreMoves(l, ttm, ply);
  int best = -INFV, moveCount = 0, nq = 0; U16 bestMove = 0, quiets[64]; const int origAlpha = alpha;
  for(int i = 0; i < l.n; i++){ pickBest(l, i); U16 m = l.m[i]; if(m == excl) continue;
    const int from = m & 63, to = (m >> 6) & 63, fl = m >> 12; const bool cap = (fl & 4) != 0, promo = (fl & 8) != 0, quiet = !cap && !promo;
    const int pcMoved = P.mb[from];
    doMove(m, UN[ply]);
    if(attackedBy(lsb(P.bb[us * 6 + KING]), P.stm, P.all)){ undoMove(m, UN[ply]); continue; }
    moveCount++; const bool gives = inCheckNow();
    if(!weak && !root && best > -MATE_BOUND && !inChk){
      if(quiet && !gives){
        if(depth <= 8 && moveCount > (improving ? 3 + depth * depth : (3 + depth * depth) / 2)){ undoMove(m, UN[ply]); continue; }
        if(depth <= 7 && ev + 90 + 100 * depth <= alpha){ undoMove(m, UN[ply]); continue; } }
      if(!pv && l.s[i] < 0 && cap && depth <= 5){ undoMove(m, UN[ply]); if(!seeGE(m, -100 * depth)) continue; doMove(m, UN[ply]); } }
    int newDepth = depth - 1, v;
    SS[ply].mv = m; SS[ply].pc = (U8)pcMoved; SS[ply].to = (U8)to;
    if(!weak && depth >= 3 && moveCount > 1 && (quiet || l.s[i] < 0)){
      int r = LMRT[imin(depth, 63)][imin(moveCount, 63)];
      if(pv) r--; if(!improving) r++; if(gives) r--; if(quiet && (m == SS[ply].k1 || m == SS[ply].k2)) r--; if(quiet) r -= HIST[us][from][to] / 6000;
      if(r < 0) r = 0; if(r > newDepth - 1) r = newDepth - 1;
      v = -search(newDepth - r, -alpha - 1, -alpha, ply + 1, true, 0);
      if(v > alpha && r > 0) v = -search(newDepth, -alpha - 1, -alpha, ply + 1, true, 0);
    } else if(!pv || moveCount > 1) v = -search(newDepth, -alpha - 1, -alpha, ply + 1, true, 0);
    else v = alpha + 1;
    if(pv && (moveCount == 1 || v > alpha)) v = -search(newDepth, -beta, -alpha, ply + 1, true, 0);
    undoMove(m, UN[ply]); if(stopFlag) return 0;
    if(v > best){ best = v; if(v > alpha){ alpha = v; bestMove = m; if(root) rootBestIter = m; if(v >= beta) break; } }
    if(quiet && nq < 64) quiets[nq++] = m; }
  if(moveCount == 0) return excl ? alpha : (inChk ? -MATE + ply : 0);
  if(best >= beta && !weak){ U16 m = bestMove; const int from = m & 63, to = (m >> 6) & 63; if(!(m >> 12 & 12)){
      int bonus = imin(170 * depth - 80, 1700); if(bonus < 0) bonus = 0;
      if(SS[ply].k1 != m){ SS[ply].k2 = SS[ply].k1; SS[ply].k1 = m; }
      histUpd(HIST[us][from][to], bonus); for(int j = 0; j < nq; j++) if(quiets[j] != m) histUpd(HIST[us][quiets[j] & 63][(quiets[j] >> 6) & 63], -bonus);
      if(ply > 0 && SS[ply - 1].mv) COUNTER[SS[ply - 1].pc][SS[ply - 1].to] = m; } }
  if(!excl && !stopFlag) ttStore(te, hit, P.key, depth, best >= beta ? B_LOW : (best > origAlpha ? B_EXACT : B_UP), best, inChk ? 0 : SS[ply].eval, bestMove, ply);
  return best; }

/* ---- driver ---- */
static int IO[8192];
static U16 rootMoves[256]; static int nRoot;
static void legalRoot(){ U16 mv[256]; int n = genMoves(mv, false); nRoot = 0; Undo u;
  for(int i = 0; i < n; i++){ doMove(mv[i], u); bool ok = !attackedBy(lsb(P.bb[(P.stm ^ 1) * 6 + KING]), P.stm, P.all); undoMove(mv[i], u); if(ok) rootMoves[nRoot++] = mv[i]; } }
static void clearSearchState(){
  for(int i = 0; i < MAXPLY + 8; i++){ SS[i].k1 = SS[i].k2 = 0; SS[i].mv = 0; SS[i].eval = -INFV; }
  for(int a = 0; a < 2; a++) for(int b = 0; b < 64; b++) for(int c = 0; c < 64; c++) HIST[a][b][c] = HIST[a][b][c] / 2;
  for(int a = 0; a < 12; a++) for(int b = 0; b < 64; b++) COUNTER[a][b] = 0; }
static int lastMode = -1, lastDepth = -1;

static void outMove(U16 m, int score, int depth){
  int pr = (m >> 12) & 8 ? ((m >> 12) & 3) + 2 : 0;
  IO[0] = (m & 63) ^ 56; IO[1] = ((m >> 6) & 63) ^ 56; IO[2] = pr; IO[3] = score; IO[4] = depth; IO[5] = nodes > 2147483000ULL ? 2147483000 : (int)nodes; IO[6] = 1; }

static int styleBonus(U16 m, int style){
  if(!style) return 0; Undo u; const int us = P.stm; const bool cap = (m >> 12) & 4; const int to = (m >> 6) & 63; int b = 0;
  doMove(m, u); bool gives = inCheckNow();
  bool hang = attackedBy(to, us ^ 1, P.all) && !attackedBy(to, us, P.all);
  undoMove(m, u);
  if(style == 1){ if(cap) b += 45; if(gives) b += 30; } else if(style == 2){ if(cap) b += 25; if(gives) b += 50; } else if(style == 3){ if(hang) b -= 60; if(!cap) b += 10; }
  return b; }

static U16 skillPick(const int* scores, double T, double oops, double mate, int style, int top, U16 topM){
  if(top > MATE_BOUND && rnd01() >= mate) return topM;
  const bool slip = rnd01() < oops; const double Tt = slip ? T * 2 + 30 : T; int sc[256]; int bs = -100000;
  for(int i = 0; i < nRoot; i++){ int s0;
    if(slip){ Undo u; doMove(rootMoves[i], u); s0 = -evaluate(); undoMove(rootMoves[i], u); } else s0 = scores[i];
    int s = imax(-3000, imin(3000, s0)) + styleBonus(rootMoves[i], style); sc[i] = s; if(s > bs) bs = s; }
  if(Tt <= 0.0001){ for(int i = 0; i < nRoot; i++) if(sc[i] == bs) return rootMoves[i]; }
  double w[256], tot = 0; for(int i = 0; i < nRoot; i++){ w[i] = pxexpneg((double)(bs - sc[i]) / Tt); tot += w[i]; }
  double r = rnd01() * tot; for(int i = 0; i < nRoot; i++){ r -= w[i]; if(r <= 0) return rootMoves[i]; }
  return rootMoves[0]; }

PX_EXPORT(px_init) void px_init(void){ px_init_impl(); }
PX_EXPORT(px_io) int* px_io(void){ return IO; }

static U64 perftRec(int d, int ply){
  if(d == 0) return 1; U16 mv[256]; int n = genMoves(mv, false); U64 t = 0;
  for(int i = 0; i < n; i++){ doMove(mv[i], UN[ply]);
    if(!attackedBy(lsb(P.bb[(P.stm ^ 1) * 6 + KING]), P.stm, P.all)) t += d == 1 ? 1 : perftRec(d - 1, ply + 1);
    undoMove(mv[i], UN[ply]); }
  return t; }
PX_EXPORT(px_perft) int px_perft(int depth){ px_init_impl(); Pos p; setupIO(IO, p); P = p; return (int)perftRec(depth, 0); }

PX_EXPORT(px_search) void px_search(void){
  px_init_impl();
  const int mode = IO[69], ms = IO[70], maxD = IO[71], qd = IO[72]; const double T = IO[73] / 1000.0, oops = IO[74] / 1000.0, mate = IO[75] / 1000.0;
  const int style = IO[76], nrep = imin(IO[78], 100); rngS = ((U64)(U32)IO[77] + 1) * 0x9E3779B97F4A7C15ULL; rnd64(); rnd64();
  Pos rp; setupIO(IO, rp); rootIdx = nrep;
  for(int i = 0; i < nrep; i++){ Pos tp; setupIO(IO + 100 + i * 67, tp); KEYS[i] = tp.key; }
  P = rp; IO[6] = 0; nodes = 0; legalRoot();
  if(nRoot == 0) return;
  if(nRoot == 1){ outMove(rootMoves[0], 0, 0); return; }
  if(mode == 0){ outMove(rootMoves[(int)(rnd64() % (U64)nRoot)], 0, 0); return; }
  if(mode != lastMode || (mode == 1 && maxD != lastDepth)){ for(U64 i = 0; i < TTN; i++) TT[i].fa = 0; lastMode = mode; lastDepth = maxD; }
  ttGen++; clearSearchState(); stopFlag = false; hardMs = ms; t0 = px_now(); rootDepth = 1; rootBestIter = 0;
  if(mode == 1){
    weak = true; qMax = qd; int npm = 0; for(int t = KNIGHT; t <= QUEEN; t++) npm += PVAL[t] * popc(P.bb[t] | P.bb[6 + t]);
    int cap = maxD + ((npm <= 2400 && maxD >= 3) ? 2 : 0); double margin = T * 7 > 60 ? T * 7 : 60;
    int scores[256], last[256]; for(int i = 0; i < nRoot; i++) last[i] = -3000; int doneDepth = 0;
    /* order root moves by a quick quiescence pass */
    for(int d = 1; d <= cap; d++){
      int cur[256], best = -INFV; bool aborted = false;
      for(int i = 0; i < nRoot; i++){ Undo u; doMove(rootMoves[i], u); int lo = best == -INFV ? -INFV : best - (int)margin;
        int v = -search(d - 1, -INFV, lo == -INFV ? INFV : -lo, 1, false, 0); undoMove(rootMoves[i], u);
        if(stopFlag){ aborted = true; break; } cur[i] = v; if(v > best) best = v; }
      if(aborted) break;
      for(int i = 0; i < nRoot; i++) last[i] = cur[i]; doneDepth = d; rootDepth = d + 1;
      /* best-first for the next depth */
      for(int i = 1; i < nRoot; i++){ int j = i; while(j > 0 && last[j] > last[j - 1]){ int ts = last[j]; last[j] = last[j - 1]; last[j - 1] = ts; U16 tm = rootMoves[j]; rootMoves[j] = rootMoves[j - 1]; rootMoves[j - 1] = tm; j--; } }
      if(best > MATE_BOUND) break; if(px_now() - t0 > ms * 0.5) break; }
    for(int i = 0; i < nRoot; i++) scores[i] = last[i];
    int top = -INFV; U16 topM = rootMoves[0]; for(int i = 0; i < nRoot; i++) if(scores[i] > top){ top = scores[i]; topM = rootMoves[i]; }
    stopFlag = false; U16 pick = skillPick(scores, T, oops, mate, style, top, topM); outMove(pick, top, doneDepth); weak = false; return; }
  weak = false; qMax = 99;
  int maxDepth = imin(maxD > 0 ? maxD : 64, MAXPLY - 10); int score = 0, prev = 0, stable = 0, doneDepth = 0; U16 best = rootMoves[0], lastBest = 0;
  for(int d = 1; d <= maxDepth; d++){
    rootDepth = d; int alpha = -INFV, beta = INFV, delta = 18; if(d >= 5){ alpha = imax(prev - delta, -INFV); beta = imin(prev + delta, INFV); }
    for(;;){ rootBestIter = 0; score = search(d, alpha, beta, 0, false, 0); if(stopFlag) break;
      if(score <= alpha){ beta = (alpha + beta) / 2; alpha = imax(score - delta, -INFV); }
      else if(score >= beta){ if(rootBestIter) best = rootBestIter; beta = imin(score + delta, INFV); }
      else break; delta += delta / 2 + 4; }
    if(stopFlag){ if(rootBestIter) best = rootBestIter; break; }
    if(rootBestIter) best = rootBestIter; prev = score; doneDepth = d;
    stable = best == lastBest ? stable + 1 : 0; lastBest = best;
    double el = px_now() - t0;
    if(score > MATE_BOUND && d >= 4) break;
    if(el >= ms * 0.45) break; if(d >= 10 && stable >= 3 && el > ms * 0.15) break; }
  outMove(best, prev, doneDepth); }
