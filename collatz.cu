// Generalized Collatz sweep: T(n) = a*n + c (n odd), n/2 (n even), a,c odd.
// Accelerated odd->odd map F(n) = (a*n+c) >> ctz(a*n+c).
// Pass A: Brent cycle detection over odd starts < M  -> cycle inventory (cycle minima).
// Pass B: classify every odd start < N: enters which cycle / exceeds window tau / fuel-out.
// Output: one JSON object per variant on stdout.
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <chrono>

typedef unsigned long long u64;
typedef long long i64;

#define CUCHECK(x) do{ cudaError_t e=(x); if(e){ fprintf(stderr,"CUDA err %s @%d\n", cudaGetErrorString(e), __LINE__); exit(1);} }while(0)

__device__ __forceinline__ int ctz64(u64 x){ return __ffsll((i64)x) - 1; }

__constant__ u64 c_mins[64];

__device__ __forceinline__ u64 stepF(u64 x, u64 a, i64 c, u64 tau, int* esc){
  if (x > tau) { *esc = 1; return x; }
  u64 m = a*x + (u64)c;
  return m >> ctz64(m);
}

__global__ void passA(u64 M, u64 a, i64 c, u64 tau, int fuel, u64* out){
  u64 idx = (u64)blockIdx.x*blockDim.x + threadIdx.x;
  u64 s = 2*idx + 1;
  if (s >= M) return;
  int esc = 0, f = fuel;
  u64 tort = s;
  u64 hare = stepF(s, a, c, tau, &esc); f--;
  u64 power = 1, lam = 1;
  while (!esc && tort != hare && f > 0){
    if (power == lam){ tort = hare; power <<= 1; lam = 0; }
    hare = stepF(hare, a, c, tau, &esc); lam++; f--;
  }
  if (esc){ out[idx] = 0; return; }
  if (tort != hare){ out[idx] = ~0ull; return; }
  u64 mn = hare, x = hare;
  for (u64 i = 0; i < lam; i++){ x = stepF(x, a, c, tau, &esc); if (x < mn) mn = x; }
  out[idx] = mn;
}

__global__ void passB(u64 N, u64 a, i64 c, u64 tau, u64 minsMax, int nmins, int fuel, int sampEsc,
                      u64* gc, u64* gstats, u64* gsamp, unsigned* gnsamp){
  __shared__ u64 sb[66];
  __shared__ u64 sst[3];
  int nt = nmins + 2;
  for (int i = threadIdx.x; i < nt; i += blockDim.x) sb[i] = 0;
  if (threadIdx.x < 3) sst[threadIdx.x] = 0;
  __syncthreads();
  u64 idx = (u64)blockIdx.x*blockDim.x + threadIdx.x;
  u64 s = 2*idx + 1;
  if (s < N){
    u64 n = s, mx = s, halv = 0;
    unsigned osteps = 0;
    int cls = -1;
    for (int it = 0; it < fuel; ++it){
      if (n <= minsMax){
        for (int j = 0; j < nmins; j++) if (n == c_mins[j]){ cls = j; break; }
        if (cls >= 0) break;
      }
      if (n > tau){ cls = nmins; break; }
      u64 m = a*n + (u64)c;
      if (m > mx) mx = m;
      int h = ctz64(m);
      n = m >> h; halv += (u64)h; osteps++;
    }
    if (cls < 0) cls = nmins + 1;
    if (cls == nmins + 1 || (cls == nmins && sampEsc)){
      unsigned k = atomicAdd(gnsamp, 1u);
      if (k < 4096) gsamp[k] = s;
    }
    atomicAdd(&sb[cls], 1ull);
    atomicAdd(&sst[0], (u64)osteps);
    atomicAdd(&sst[1], halv);
    atomicMax(&sst[2], mx);
  }
  __syncthreads();
  for (int i = threadIdx.x; i < nt; i += blockDim.x) if (sb[i]) atomicAdd(&gc[i], sb[i]);
  if (threadIdx.x == 0){
    atomicAdd(&gstats[0], sst[0]);
    atomicAdd(&gstats[1], sst[1]);
    atomicMax(&gstats[2], sst[2]);
  }
}

// ---- host ----
static u64 hstep(u64 x, u64 a, i64 c, u64 tau, int* esc){
  if (x > tau){ *esc = 1; return x; }
  u64 m = a*x + (u64)c;
  int h = __builtin_ctzll(m);
  return m >> h;
}

struct Variant { u64 a; i64 c; u64 N; };

int main(int argc, char** argv){
  const u64 M = 1ull<<22;          // pass A start range (odd starts)
  const int FUEL_A = 1<<14;
  const int FUEL_B = 8192;

  std::vector<Variant> grid;
  auto add = [&](u64 a, i64 c, u64 N){ grid.push_back({a,c,N}); };
  add(1,1,1ull<<30);
  add(3,-1,1ull<<32); add(3,1,1ull<<32);
  for (i64 c = 3; c <= 19; c += 2) add(3,c,1ull<<32);
  for (i64 c = 1; c <= 11; c += 2) add(5,c,1ull<<30);
  for (i64 c = 1; c <= 11; c += 2) add(7,c,1ull<<30);
  for (i64 c = 1; c <= 11; c += 2) add(9,c,1ull<<30);
  for (i64 c = 1; c <= 5;  c += 2) add(11,c,1ull<<30);
  for (i64 c = 1; c <= 3;  c += 2) add(13,c,1ull<<30);
  for (i64 c = 1; c <= 5;  c += 2) add(15,c,1ull<<30);

  if (argc == 3){ // filter: ./collatz_gpu a c
    u64 fa = strtoull(argv[1],0,10); i64 fc = strtoll(argv[2],0,10);
    std::vector<Variant> g2;
    for (auto& v : grid) if (v.a==fa && v.c==fc) g2.push_back(v);
    grid = g2;
  }

  u64 *dA, *dc, *dst, *dsamp; unsigned *dn;
  CUCHECK(cudaMalloc(&dA, (M/2)*sizeof(u64)));
  CUCHECK(cudaMalloc(&dc, 66*sizeof(u64)));
  CUCHECK(cudaMalloc(&dst, 3*sizeof(u64)));
  CUCHECK(cudaMalloc(&dsamp, 4096*sizeof(u64)));
  CUCHECK(cudaMalloc(&dn, sizeof(unsigned)));
  std::vector<u64> hA(M/2);

  for (auto& v : grid){
    u64 tau = (~0ull - 1024) / v.a;
    if (tau > (1ull<<62)) tau = 1ull<<62;
    auto t0 = std::chrono::steady_clock::now();

    // Pass A
    int bs = 256;
    u64 nthA = M/2;
    passA<<<(unsigned)((nthA+bs-1)/bs), bs>>>(M, v.a, v.c, tau, FUEL_A, dA);
    CUCHECK(cudaDeviceSynchronize());
    CUCHECK(cudaMemcpy(hA.data(), dA, (M/2)*sizeof(u64), cudaMemcpyDeviceToHost));
    u64 aesc = 0, afo = 0;
    std::vector<u64> mins;
    for (u64 x : hA){
      if (x == 0) aesc++;
      else if (x == ~0ull) afo++;
      else mins.push_back(x);
    }
    std::sort(mins.begin(), mins.end());
    mins.erase(std::unique(mins.begin(), mins.end()), mins.end());
    if (mins.size() > 64){ fprintf(stderr, "WARN a=%llu c=%lld: >64 cycles, truncating\n", v.a, v.c); mins.resize(64); }
    int nm = (int)mins.size();
    u64 minsMax = nm ? mins.back() : 0;

    // cycle details on host
    struct Cyc { u64 mn, k, H, mx; std::vector<u64> mem; };
    std::vector<Cyc> cycs;
    for (u64 mn : mins){
      Cyc cy; cy.mn = mn; cy.k = 0; cy.H = 0; cy.mx = mn;
      u64 x = mn; int esc = 0;
      do {
        if (cy.mem.size() < 24) cy.mem.push_back(x);
        u64 m = v.a*x + (u64)v.c;
        if (m > cy.mx) cy.mx = m;
        int h = __builtin_ctzll(m);
        cy.H += h; cy.k++;
        x = m >> h;
        (void)esc;
      } while (x != mn && cy.k < (1u<<20));
      cycs.push_back(cy);
    }

    // Pass B
    if (nm) CUCHECK(cudaMemcpyToSymbol(c_mins, mins.data(), nm*sizeof(u64)));
    CUCHECK(cudaMemset(dc, 0, 66*sizeof(u64)));
    CUCHECK(cudaMemset(dst, 0, 3*sizeof(u64)));
    CUCHECK(cudaMemset(dn, 0, sizeof(unsigned)));
    u64 nthB = v.N/2;
    int sampEsc = (v.a <= 3);
    passB<<<(unsigned)((nthB+bs-1)/bs), bs>>>(v.N, v.a, v.c, tau, minsMax, nm, FUEL_B, sampEsc, dc, dst, dsamp, dn);
    CUCHECK(cudaDeviceSynchronize());
    std::vector<u64> hc(66), hst(3);
    unsigned hn = 0;
    CUCHECK(cudaMemcpy(hc.data(), dc, 66*sizeof(u64), cudaMemcpyDeviceToHost));
    CUCHECK(cudaMemcpy(hst.data(), dst, 3*sizeof(u64), cudaMemcpyDeviceToHost));
    CUCHECK(cudaMemcpy(&hn, dn, sizeof(unsigned), cudaMemcpyDeviceToHost));
    std::vector<u64> hsamp(std::min(hn, 4096u));
    if (hn) CUCHECK(cudaMemcpy(hsamp.data(), dsamp, hsamp.size()*sizeof(u64), cudaMemcpyDeviceToHost));

    double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

    // JSON line
    printf("{\"a\":%llu,\"c\":%lld,\"N\":%llu,\"M\":%llu,\"tau\":%llu,\"fuelA\":%d,\"fuelB\":%d,",
           v.a, v.c, v.N, M, tau, FUEL_A, FUEL_B);
    printf("\"passA\":{\"escape\":%llu,\"fuelout\":%llu},", aesc, afo);
    printf("\"cycles\":[");
    for (size_t i = 0; i < cycs.size(); i++){
      auto& cy = cycs[i];
      printf("%s{\"min\":%llu,\"k\":%llu,\"H\":%llu,\"len\":%llu,\"max\":%llu,\"members\":[",
             i?",":"", cy.mn, cy.k, cy.H, cy.k+cy.H, cy.mx);
      for (size_t j = 0; j < cy.mem.size(); j++) printf("%s%llu", j?",":"", cy.mem[j]);
      printf("]}");
    }
    printf("],\"passB\":{\"counts\":[");
    for (int i = 0; i < nm; i++) printf("%s%llu", i?",":"", hc[i]);
    printf("],\"escape\":%llu,\"fuelout\":%llu,\"oddsteps\":%llu,\"halvings\":%llu,\"maxexc\":%llu,\"nsamp\":%u,\"samples\":[",
           hc[nm], hc[nm+1], hst[0], hst[1], hst[2], hn);
    for (size_t i = 0; i < hsamp.size() && i < 64; i++) printf("%s%llu", i?",":"", hsamp[i]);
    printf("]},\"secs\":%.3f}\n", secs);
    fflush(stdout);
    fprintf(stderr, "done a=%llu c=%lld  cycles=%d  esc=%llu  fo=%llu  %.1fs\n",
            v.a, v.c, nm, hc[nm], hc[nm+1], secs);
  }
  return 0;
}
