// universal.cu — machine verification of the sharpened universal-cycle theorems
// (companion to CollatzTheory.lean §5). Accelerated odd->odd map:
//     F_{a,c}(x) = (a*x + c) >> v2(a*x + c)
//
// S1 rigidity grid   : ALL odd a,c < 2^20 (2.75e11 pairs):
//                        F(c) == oddpart(a+1)*c            (master formula)
//                        F(c) == c  <=>  a+1 power of two  (Mersenne iff)
// S2 fixed-pt census : ALL odd a,c < 512, ALL odd x < 2^22 (1.37e11 triples):
//                        every fixed point F(x)==x matches the one-step law
//                        x | c  &&  a + c/x power of two; CPU independently
//                        enumerates the law's predictions; sets must be EQUAL.
// S3 U-catalog       : ALL odd a < 2^24: is 1 periodic under F_{a,1}?
//                        (return-to-1 within fuel 4096, u64 window). Every hit
//                        is a UNIVERSAL cycle family {c*y_i} for every odd c.
// S4 scaling fuzz    : 2^33 pseudorandom (a,d,e,u), d,e odd:
//                        F_{a,d*e}(d*u) == d * F_{a,e}(u)   (master identity)
//
// Output: JSON lines on stdout (redirect to results/universal.jsonl);
//         human summary on stderr. Exit code 1 on ANY violation.
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <chrono>

typedef unsigned long long u64;

#define CUCHECK(x) do{ cudaError_t e=(x); if(e){ fprintf(stderr,"CUDA err %s @%d\n", cudaGetErrorString(e), __LINE__); exit(1);} }while(0)

__device__ __forceinline__ int ctz64(u64 x){ return __ffsll((long long)x) - 1; }
__device__ __forceinline__ bool isPow2(u64 x){ return x && !(x & (x - 1)); }

// ---------------- S1: rigidity grid ----------------
__global__ void s1_rigidity(u64 halfA, u64 halfC, u64* nFixed, u64* nIffViol, u64* nFormViol){
  u64 total = halfA * halfC;
  u64 stride = (u64)gridDim.x * blockDim.x;
  u64 fixed_ = 0, iffv = 0, formv = 0;
  for (u64 i = (u64)blockIdx.x*blockDim.x + threadIdx.x; i < total; i += stride){
    u64 a = 2*(i / halfC) + 1;
    u64 c = 2*(i % halfC) + 1;
    u64 t = a*c + c;                    // <= (2^20)(2^20) = 2^40, no overflow
    u64 F = t >> ctz64(t);
    u64 ap1 = a + 1;
    u64 m = ap1 >> ctz64(ap1);          // oddpart(a+1)
    bool fx  = (F == c);
    bool mer = isPow2(ap1);
    if (fx) fixed_++;
    if (fx != mer) iffv++;              // Mersenne iff
    if (F != m * c) formv++;            // master formula F(c) = oddpart(a+1)*c
  }
  atomicAdd(nFixed, fixed_); atomicAdd(nIffViol, iffv); atomicAdd(nFormViol, formv);
}

// ---------------- S2: fixed-point census ----------------
__global__ void s2_census(u64 halfAC, u64 halfX, u64* nFix, u64* nMatch,
                          u64* buf, unsigned* nbuf, unsigned bufCap){
  u64 total = halfAC * halfAC * halfX;
  u64 stride = (u64)gridDim.x * blockDim.x;
  u64 fix_ = 0, match_ = 0;
  for (u64 i = (u64)blockIdx.x*blockDim.x + threadIdx.x; i < total; i += stride){
    u64 a = 2*(i / (halfAC*halfX)) + 1;
    u64 r = i % (halfAC*halfX);
    u64 c = 2*(r / halfX) + 1;
    u64 x = 2*(r % halfX) + 1;
    u64 t = a*x + c;                    // < 512*2^22 + 512 < 2^32
    u64 F = t >> ctz64(t);
    if (F == x){
      fix_++;
      if (c % x == 0 && isPow2(a + c/x)) match_++;   // the one-step law
      unsigned k = atomicAdd(nbuf, 1u);
      if (k < bufCap) buf[k] = (a<<40) | (c<<24) | x;
    }
  }
  atomicAdd(nFix, fix_); atomicAdd(nMatch, match_);
}

// ---------------- S3: universal-family catalog ----------------
__global__ void s3_ucatalog(u64 halfA, int fuel, u64* counts,
                            u64* buf, unsigned* nbuf, unsigned bufCap){
  u64 stride = (u64)gridDim.x * blockDim.x;
  for (u64 i = (u64)blockIdx.x*blockDim.x + threadIdx.x; i < halfA; i += stride){
    u64 a = 2*i + 1;
    u64 tau = (~0ull - 1) / a;          // a*x+1 <= 2^64-1 whenever x <= tau
    u64 x = 1; int cls = 2; int per = 0; // 0 periodic / 1 escape / 2 fuelout
    for (int s = 1; s <= fuel; s++){
      if (x > tau){ cls = 1; break; }
      u64 t = a*x + 1;
      x = t >> ctz64(t);
      if (x == 1){ cls = 0; per = s; break; }
    }
    atomicAdd(&counts[cls], 1ull);
    if (cls == 0){
      unsigned k = atomicAdd(nbuf, 1u);
      if (k < bufCap) buf[k] = (a<<16) | (u64)per;
    }
  }
}

// ---------------- S4: scaling-identity fuzz ----------------
__device__ __forceinline__ u64 splitmix64(u64 z){
  z += 0x9E3779B97F4A7C15ull;
  z = (z ^ (z>>30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z>>27)) * 0x94D049BB133111EBull;
  return z ^ (z>>31);
}

__global__ void s4_fuzz(u64 trials, u64* nViol){
  u64 stride = (u64)gridDim.x * blockDim.x;
  u64 viol = 0;
  for (u64 i = (u64)blockIdx.x*blockDim.x + threadIdx.x; i < trials; i += stride){
    u64 a = splitmix64(4*i+0) & ((1u<<20)-1);          // arbitrary (any parity)
    u64 d = (splitmix64(4*i+1) & ((1u<<19)-1)) | 1;    // odd (theorem hypothesis)
    u64 e = (splitmix64(4*i+2) & ((1u<<20)-1)) | 1;    // odd (keeps a*u+e >= 1)
    u64 u = splitmix64(4*i+3) & ((1u<<19)-1);          // arbitrary (any parity)
    u64 t2 = a*u + e;                    // < 2^39 + 2^20
    u64 f2 = t2 >> ctz64(t2);
    u64 t1 = a*(d*u) + d*e;              // < 2^58
    u64 f1 = t1 >> ctz64(t1);
    if (f1 != d*f2) viol++;
  }
  atomicAdd(nViol, viol);
}

// ---------------- host ----------------
static double secsSince(std::chrono::steady_clock::time_point t0){
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}
static bool hIsPow2(u64 x){ return x && !(x & (x-1)); }

int main(){
  int fails = 0;
  const int BLK = 256, GRD = 8192;

  u64 *d6; unsigned *dn;
  CUCHECK(cudaMalloc(&d6, 6*sizeof(u64)));
  CUCHECK(cudaMalloc(&dn, sizeof(unsigned)));

  // ==== S1 ====
  {
    const u64 halfA = 1ull<<19, halfC = 1ull<<19;      // odd a,c < 2^20
    CUCHECK(cudaMemset(d6, 0, 3*sizeof(u64)));
    auto t0 = std::chrono::steady_clock::now();
    s1_rigidity<<<GRD, BLK>>>(halfA, halfC, d6+0, d6+1, d6+2);
    CUCHECK(cudaDeviceSynchronize());
    u64 h[3]; CUCHECK(cudaMemcpy(h, d6, 3*sizeof(u64), cudaMemcpyDeviceToHost));
    double dt = secsSince(t0);
    u64 nMer = 0; for (u64 a = 1; a < (1ull<<20); a += 2) if (hIsPow2(a+1)) nMer++;
    u64 expected = nMer * halfC;
    bool ok = (h[1]==0 && h[2]==0 && h[0]==expected);
    if (!ok) fails++;
    printf("{\"section\":\"S1\",\"oddAbelow\":%llu,\"oddCbelow\":%llu,\"pairs\":%llu,"
           "\"nFixed\":%llu,\"expectedFixed\":%llu,\"mersenneCount\":%llu,"
           "\"iffViolations\":%llu,\"formulaViolations\":%llu,\"pass\":%s,\"secs\":%.3f}\n",
           1ull<<20, 1ull<<20, halfA*halfC, h[0], expected, nMer, h[1], h[2],
           ok?"true":"false", dt);
    fprintf(stderr, "S1 rigidity: %llu pairs, fixed=%llu (expected %llu), iffViol=%llu, formViol=%llu  [%s] %.1fs\n",
            halfA*halfC, h[0], expected, h[1], h[2], ok?"PASS":"FAIL", dt);
  }

  // ==== S2 ====
  {
    const u64 halfAC = 256, halfX = 1ull<<21;          // odd a,c < 512, odd x < 2^22
    const unsigned CAP = 1u<<20;
    u64* dbuf; CUCHECK(cudaMalloc(&dbuf, CAP*sizeof(u64)));
    CUCHECK(cudaMemset(d6, 0, 2*sizeof(u64)));
    CUCHECK(cudaMemset(dn, 0, sizeof(unsigned)));
    auto t0 = std::chrono::steady_clock::now();
    s2_census<<<GRD, BLK>>>(halfAC, halfX, d6+0, d6+1, dbuf, dn, CAP);
    CUCHECK(cudaDeviceSynchronize());
    u64 h[2]; unsigned hn;
    CUCHECK(cudaMemcpy(h, d6, 2*sizeof(u64), cudaMemcpyDeviceToHost));
    CUCHECK(cudaMemcpy(&hn, dn, sizeof(unsigned), cudaMemcpyDeviceToHost));
    std::vector<u64> gpu(std::min(hn, CAP));
    if (hn) CUCHECK(cudaMemcpy(gpu.data(), dbuf, gpu.size()*sizeof(u64), cudaMemcpyDeviceToHost));
    double dt = secsSince(t0);
    // CPU: independent enumeration from the one-step law
    std::vector<u64> cpu;
    for (u64 a = 1; a < 2*halfAC; a += 2)
      for (u64 c = 1; c < 2*halfAC; c += 2)
        for (u64 d = 1; d <= c; d += 2)
          if (c % d == 0 && hIsPow2(a + d) && (c/d) < 2*halfX)
            cpu.push_back((a<<40) | (c<<24) | (c/d));
    std::sort(gpu.begin(), gpu.end());
    std::sort(cpu.begin(), cpu.end());
    bool setEq = (gpu == cpu);
    bool ok = (h[0]==h[1]) && setEq && (hn == gpu.size()) && (hn == h[0]);
    if (!ok) fails++;
    printf("{\"section\":\"S2\",\"oddACbelow\":%llu,\"oddXbelow\":%llu,\"triples\":%llu,"
           "\"nFixedFound\":%llu,\"nMatchingLaw\":%llu,\"cpuPredicted\":%zu,\"setEqual\":%s,"
           "\"pass\":%s,\"secs\":%.3f,\"entries\":[",
           2*halfAC, 2*halfX, halfAC*halfAC*halfX, h[0], h[1], cpu.size(),
           setEq?"true":"false", ok?"true":"false", dt);
    for (size_t i = 0; i < gpu.size(); i++){
      u64 v = gpu[i];
      printf("%s[%llu,%llu,%llu]", i?",":"", v>>40, (v>>24)&0xFFFF, v&0xFFFFFF);
    }
    printf("]}\n");
    fprintf(stderr, "S2 census: fixed=%llu match=%llu cpu=%zu setEq=%d  [%s] %.1fs\n",
            h[0], h[1], cpu.size(), (int)setEq, ok?"PASS":"FAIL", dt);
    CUCHECK(cudaFree(dbuf));
  }

  // ==== S3 ====
  {
    const u64 halfA = 1ull<<23;                        // odd a < 2^24
    const int FUEL = 4096;
    const unsigned CAP = 4096;
    u64* dbuf; CUCHECK(cudaMalloc(&dbuf, CAP*sizeof(u64)));
    CUCHECK(cudaMemset(d6, 0, 3*sizeof(u64)));
    CUCHECK(cudaMemset(dn, 0, sizeof(unsigned)));
    auto t0 = std::chrono::steady_clock::now();
    s3_ucatalog<<<GRD, BLK>>>(halfA, FUEL, d6, dbuf, dn, CAP);
    CUCHECK(cudaDeviceSynchronize());
    u64 h[3]; unsigned hn;
    CUCHECK(cudaMemcpy(h, d6, 3*sizeof(u64), cudaMemcpyDeviceToHost));
    CUCHECK(cudaMemcpy(&hn, dn, sizeof(unsigned), cudaMemcpyDeviceToHost));
    std::vector<u64> cat(std::min(hn, CAP));
    if (hn) CUCHECK(cudaMemcpy(cat.data(), dbuf, cat.size()*sizeof(u64), cudaMemcpyDeviceToHost));
    double dt = secsSince(t0);
    std::sort(cat.begin(), cat.end());
    // every Mersenne a < 2^24 must be present with period 1
    bool merOk = true;
    for (int k = 1; k <= 24; k++){
      u64 a = (1ull<<k) - 1; if (a >= (1ull<<24)) break;
      bool found = false;
      for (u64 v : cat) if ((v>>16) == a && (v&0xFFFF) == 1) found = true;
      if (!found) merOk = false;
    }
    bool ok = merOk && (hn == cat.size());
    if (!ok) fails++;
    printf("{\"section\":\"S3\",\"oddAbelow\":%llu,\"fuel\":%d,"
           "\"periodic\":%llu,\"escape\":%llu,\"fuelout\":%llu,"
           "\"allMersennePeriod1\":%s,\"pass\":%s,\"secs\":%.3f,\"catalog\":[",
           2*halfA, FUEL, h[0], h[1], h[2], merOk?"true":"false", ok?"true":"false", dt);
    for (size_t i = 0; i < cat.size(); i++)
      printf("%s[%llu,%llu]", i?",":"", cat[i]>>16, cat[i]&0xFFFF);
    printf("]}\n");
    fprintf(stderr, "S3 catalog: periodic=%llu escape=%llu fuelout=%llu entries=%u  [%s] %.1fs\n",
            h[0], h[1], h[2], hn, ok?"PASS":"FAIL", dt);
    for (u64 v : cat)
      if (!hIsPow2((v>>16) + 1))
        fprintf(stderr, "   non-Mersenne universal family: a=%llu period=%llu\n", v>>16, v&0xFFFF);
    CUCHECK(cudaFree(dbuf));
  }

  // ==== S4 ====
  {
    const u64 TRIALS = 1ull<<33;
    CUCHECK(cudaMemset(d6, 0, sizeof(u64)));
    auto t0 = std::chrono::steady_clock::now();
    s4_fuzz<<<GRD, BLK>>>(TRIALS, d6);
    CUCHECK(cudaDeviceSynchronize());
    u64 h; CUCHECK(cudaMemcpy(&h, d6, sizeof(u64), cudaMemcpyDeviceToHost));
    double dt = secsSince(t0);
    bool ok = (h == 0);
    if (!ok) fails++;
    printf("{\"section\":\"S4\",\"trials\":%llu,\"violations\":%llu,\"pass\":%s,\"secs\":%.3f}\n",
           TRIALS, h, ok?"true":"false", dt);
    fprintf(stderr, "S4 fuzz: %llu trials, viol=%llu  [%s] %.1fs\n", TRIALS, h, ok?"PASS":"FAIL", dt);
  }

  fprintf(stderr, fails ? "== UNIVERSAL VERIFICATION: %d SECTION(S) FAILED ==\n"
                        : "== UNIVERSAL VERIFICATION: ALL SECTIONS PASS ==\n", fails);
  return fails ? 1 : 0;
}
