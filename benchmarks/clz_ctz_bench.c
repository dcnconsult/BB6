/*
 * clz_ctz_bench.c
 *
 * Hardware Benchmark & Bit-Exact Verification Suite for Transfer #2:
 * O(1) Scalar Loop Summarization via p-Adic Ghost Shifts (TZCNT / LZCNT)
 *
 * Portable across MSVC (cl /O2 /Oi /arch:AVX2) and GCC/Clang (-O3 -march=native).
 *
 * Kernels benchmarked:
 *   1. CTZ-K1: Antihydra Mod-32 Principal Deficit Loop T_{-1}(z) = (81z+57)/16 (v=4, z*=-57/65)
 *   2. CTZ-K2: Antihydra Odd-Run Collatz Sweep z -> (3z+1)/2 (v=1, z*=-1)
 *   3. CTZ-K3: Antihydra Neutral Relay Loop T_0(z) = (27z+15)/8 (v=3, z*=-15/19)
 *   4. CLZ-K4: Cryptid A.2 / A.10 Phase-I Doubling Shuttle (beta=3, gamma=2, theta=4, u*=-3)
 *   5. CLZ-K5: Cryptid A.5 / BMO 5 Phase-I Doubling Shuttle (beta=5, gamma=3, theta=3, u*=-5)
 *   6. CLZ-K6: Cryptid AppC_1 Chained Two-Loop Doubling Epoch E2 -> E1 (X*=-2)
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_MSC_VER)
  #include <intrin.h>
  #define WIN32_LEAN_AND_MEAN
  #include <windows.h>
  #define NOINLINE    __declspec(noinline)
  #define FORCEINLINE __forceinline
  static FORCEINLINE uint32_t ctz64_hw(uint64_t x) {
      return (uint32_t)_tzcnt_u64(x);
  }
  static FORCEINLINE uint32_t lzcnt64_hw(uint64_t x) {
      return (uint32_t)_lzcnt_u64(x);
  }
  static FORCEINLINE uint64_t read_tsc(void) {
      return __rdtsc();
  }
  static double now_sec(void) {
      static LARGE_INTEGER freq = {0};
      LARGE_INTEGER counter;
      if (freq.QuadPart == 0) {
          QueryPerformanceFrequency(&freq);
      }
      QueryPerformanceCounter(&counter);
      return (double)counter.QuadPart / (double)freq.QuadPart;
  }
#else
  #include <time.h>
  #include <x86intrin.h>
  #define NOINLINE    __attribute__((noinline))
  #define FORCEINLINE inline __attribute__((always_inline))
  static FORCEINLINE uint32_t ctz64_hw(uint64_t x) {
      return x ? (uint32_t)__builtin_ctzll(x) : 64u;
  }
  static FORCEINLINE uint32_t lzcnt64_hw(uint64_t x) {
      return x ? (uint32_t)__builtin_clzll(x) : 64u;
  }
  static FORCEINLINE uint64_t read_tsc(void) {
      return __rdtsc();
  }
  static double now_sec(void) {
      struct timespec ts;
      clock_gettime(CLOCK_MONOTONIC, &ts);
      return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
  }
#endif

typedef struct {
    uint64_t u;
    uint64_t r;
    uint64_t steps;
} LoopOut;

/* Precomputed odd-multiplier power tables fitting cleanly in uint64_t */
static const uint64_t POW81[11] = {
    1ULL,
    81ULL,
    6561ULL,
    531441ULL,
    43046721ULL,
    3486784401ULL,
    282429536481ULL,
    22876792454961ULL,
    1853020188851841ULL,
    150094635296999121ULL,
    12157665459056928801ULL
};

static const uint64_t POW27[14] = {
    1ULL,
    27ULL,
    729ULL,
    19683ULL,
    531441ULL,
    14348907ULL,
    387420489ULL,
    10460353203ULL,
    282429536481ULL,
    7625597484987ULL,
    205891132094649ULL,
    5559060566555523ULL,
    150094635296999121ULL,
    4052555153018976267ULL
};

static const uint64_t POW3[41] = {
    1ULL, 3ULL, 9ULL, 27ULL, 81ULL, 243ULL, 729ULL, 2187ULL,
    6561ULL, 19683ULL, 59049ULL, 177147ULL, 531441ULL, 1594323ULL,
    4782969ULL, 14348907ULL, 43046721ULL, 129140163ULL, 387420489ULL,
    1162261467ULL, 3486784401ULL, 10460353203ULL, 31381059609ULL,
    94143178827ULL, 282429536481ULL, 847288609443ULL, 2541865828329ULL,
    7625597484987ULL, 22876792454961ULL, 68630377364883ULL,
    205891132094649ULL, 617673396283947ULL, 1853020188851841ULL,
    5559060566555523ULL, 16677181699666569ULL, 50031545098999707ULL,
    150094635296999121ULL, 450283905890997363ULL, 1350851717672992089ULL,
    4052555153018976267ULL, 12157665459056928801ULL
};

/*
 * Exact 2-adic modular inverses mod 2^64 for division-free ghost unshifting:
 * Since Phi_m = (A - 2^v) * z_m + B is guaranteed congruent to B mod (A - 2^v),
 * (Phi_m - B) / (A - 2^v) is an exact integer division on [0, 2^64), replaced
 * by a single 64-bit integer multiply by (A - 2^v)^{-1} mod 2^64.
 */
static const uint64_t INV65_U64 = 1135184250689818561ULL; /* 65 * INV65_U64 == 1 mod 2^64 */
static const uint64_t INV19_U64 = 9708812670373448219ULL; /* 19 * INV19_U64 == 1 mod 2^64 */

/* ============================================================================
 * 1. CTZ-K1: Antihydra Mod-32 Principal Deficit Loop T_{-1}(z) = (81z+57)/16
 * ============================================================================ */

NOINLINE LoopOut k1_antihydra_tneg1_naive(uint64_t z, uint64_t c) {
    uint64_t steps = 0;
    while (((81ULL * z + 57ULL) & 15ULL) == 0ULL && c >= 3ULL) {
        z = (81ULL * z + 57ULL) >> 4;
        c -= 1ULL;
        steps += 1ULL;
    }
    LoopOut out = {z, c, steps};
    return out;
}

NOINLINE LoopOut k1_antihydra_tneg1_ghost(uint64_t z, uint64_t c) {
    uint64_t phi = 65ULL * z + 57ULL;
    uint64_t m_val = (uint64_t)(ctz64_hw(phi) >> 2);
    uint64_t m_guard = (c >= 3ULL) ? (c - 2ULL) : 0ULL;
    uint64_t m = (m_val < m_guard) ? m_val : m_guard;
    uint64_t phi_m = POW81[m] * (phi >> (4U * (uint32_t)m));
    uint64_t z_m = (phi_m - 57ULL) * INV65_U64;
    LoopOut out = {z_m, c - m, m};
    return out;
}

/* ============================================================================
 * 2. CTZ-K2: Antihydra Odd-Run Inner Collatz Sweep z -> (3z+1)/2
 * ============================================================================ */

NOINLINE LoopOut k2_antihydra_odd_naive(uint64_t z, uint64_t c) {
    uint64_t steps = 0;
    while ((z & 1ULL) == 1ULL && c >= 1ULL) {
        z = (3ULL * z + 1ULL) >> 1;
        c -= 1ULL;
        steps += 1ULL;
    }
    LoopOut out = {z, c, steps};
    return out;
}

NOINLINE LoopOut k2_antihydra_odd_ghost(uint64_t z, uint64_t c) {
    uint64_t phi = z + 1ULL;
    uint64_t m_val = (uint64_t)ctz64_hw(phi);
    uint64_t m = (m_val < c) ? m_val : c;
    uint64_t z_m = POW3[m] * (phi >> (uint32_t)m) - 1ULL;
    LoopOut out = {z_m, c - m, m};
    return out;
}

/* ============================================================================
 * 3. CTZ-K3: Antihydra Neutral Relay Loop T_0(z) = (27z+15)/8 (v=3, z*=-15/19)
 * ============================================================================ */

NOINLINE LoopOut k3_antihydra_t0_naive(uint64_t z, uint64_t cap) {
    uint64_t steps = 0;
    while (((27ULL * z + 15ULL) & 7ULL) == 0ULL && steps < cap) {
        z = (27ULL * z + 15ULL) >> 3;
        steps += 1ULL;
    }
    LoopOut out = {z, cap - steps, steps};
    return out;
}

NOINLINE LoopOut k3_antihydra_t0_ghost(uint64_t z, uint64_t cap) {
    uint64_t phi = 19ULL * z + 15ULL;
    uint32_t tz = ctz64_hw(phi);
    uint64_t m_val = (uint64_t)(tz / 3U);
    uint64_t m = (m_val < cap) ? m_val : cap;
    uint64_t phi_m = POW27[m] * (phi >> (3U * (uint32_t)m));
    uint64_t z_m = (phi_m - 15ULL) * INV19_U64;
    LoopOut out = {z_m, cap - m, m};
    return out;
}

/* ============================================================================
 * 4. CLZ-K4: Cryptid A.2 / A.10 Phase-I Doubler (beta=3, gamma=2, theta=4, u*=-3)
 *    while (R >= 2*L + 4) { R -= (2*L + 2); L = 2*L + 3; }
 *    U0 = L + 3; C(j) = 2*U0*(2^j - 1) - 4*j; T(j) = (2*U0 << j) - 2*U0 - 4*(j-1) - 2
 * ============================================================================ */

NOINLINE LoopOut k4_cousin_a2_a10_naive(uint64_t L, uint64_t R) {
    uint64_t j = 0;
    while (R >= 2ULL * L + 4ULL) {
        R -= (2ULL * L + 2ULL);
        L = 2ULL * L + 3ULL;
        j += 1ULL;
    }
    LoopOut out = {L, R, j};
    return out;
}

static FORCEINLINE uint64_t k4_thresh(uint64_t U0, uint64_t j) {
    return ((2ULL * U0) << (uint32_t)j) - 2ULL * U0 - 4ULL * (j - 1ULL) - 2ULL;
}

NOINLINE LoopOut k4_cousin_a2_a10_ghost(uint64_t L, uint64_t R) {
    if (R < 2ULL * L + 4ULL) {
        LoopOut early = {L, R, 0ULL};
        return early;
    }
    uint64_t U0 = L + 3ULL;
    uint64_t W = R + 2ULL * U0 + 2ULL; /* >= 4*U0 since R >= 2*L + 4 */
    uint64_t j = (uint64_t)(lzcnt64_hw(U0) - lzcnt64_hw(W) - 2U);
    j += (uint64_t)(R >= k4_thresh(U0, j + 1ULL));
    j += (uint64_t)(R >= k4_thresh(U0, j + 1ULL));
    uint64_t Uj = U0 << (uint32_t)j;
    uint64_t consumed = 2ULL * (Uj - U0) - 4ULL * j;
    LoopOut out = {Uj - 3ULL, R - consumed, j};
    return out;
}

/* ============================================================================
 * 5. CLZ-K5: Cryptid A.5 / BMO 5 Phase-I Doubler (beta=5, gamma=3, theta=3, u*=-5)
 *    while (R >= 2*L + 3) { R -= (2*L + 3); L = 2*L + 5; }
 *    U0 = L + 5; C(j) = 2*U0*(2^j - 1) - 7*j; T(j) = (2*U0 << j) - 2*U0 - 7*(j-1) - 7
 * ============================================================================ */

NOINLINE LoopOut k5_cousin_a5_naive(uint64_t L, uint64_t R) {
    uint64_t j = 0;
    while (R >= 2ULL * L + 3ULL) {
        R -= (2ULL * L + 3ULL);
        L = 2ULL * L + 5ULL;
        j += 1ULL;
    }
    LoopOut out = {L, R, j};
    return out;
}

static FORCEINLINE uint64_t k5_thresh(uint64_t U0, uint64_t j) {
    return ((2ULL * U0) << (uint32_t)j) - 2ULL * U0 - 7ULL * (j - 1ULL) - 7ULL;
}

NOINLINE LoopOut k5_cousin_a5_ghost(uint64_t L, uint64_t R) {
    if (R < 2ULL * L + 3ULL) {
        LoopOut early = {L, R, 0ULL};
        return early;
    }
    uint64_t U0 = L + 5ULL;
    uint64_t W = R + 2ULL * U0 + 7ULL; /* >= 4*U0 since R >= 2*L + 3 */
    uint64_t j = (uint64_t)(lzcnt64_hw(U0) - lzcnt64_hw(W) - 2U);
    j += (uint64_t)(R >= k5_thresh(U0, j + 1ULL));
    j += (uint64_t)(R >= k5_thresh(U0, j + 1ULL));
    uint64_t Uj = U0 << (uint32_t)j;
    uint64_t consumed = 2ULL * (Uj - U0) - 7ULL * j;
    LoopOut out = {Uj - 5ULL, R - consumed, j};
    return out;
}

/* ============================================================================
 * 6. CLZ-K6: Cryptid AppC_1 Chained Two-Loop Epoch (E2 -> E1, X* = -2)
 *    Input: (L >= 2, R >= 0) -> x = 2, k = L - 2
 *    Loop 1 (E2): while (k >= x + 1) { k -= (x + 1); x = 2*x + 2; }
 *    Bridge:      X = 2*x + 2; z = R + 2*k + 1;
 *    Loop 2 (E1): while (z >= 2*X + 2) { z -= (2*X + 2); X = 2*X + 2; }
 * ============================================================================ */

NOINLINE LoopOut k6_appc1_chained_naive(uint64_t L, uint64_t R) {
    uint64_t x = 2ULL;
    uint64_t k = L - 2ULL;
    uint64_t steps = 0ULL;
    while (k >= x + 1ULL) {
        k -= (x + 1ULL);
        x = 2ULL * x + 2ULL;
        steps += 1ULL;
    }
    uint64_t X = 2ULL * x + 2ULL;
    uint64_t z = R + 2ULL * k + 1ULL;
    while (z >= 2ULL * X + 2ULL) {
        z -= (2ULL * X + 2ULL);
        X = 2ULL * X + 2ULL;
        steps += 1ULL;
    }
    LoopOut out = {X, z, steps};
    return out;
}

static FORCEINLINE uint64_t k6_t1(uint64_t U0, uint64_t j) {
    return (U0 << (uint32_t)j) - U0 - j;
}

static FORCEINLINE uint64_t k6_t2(uint64_t V0, uint64_t j) {
    return ((2ULL * V0) << (uint32_t)j) - 2ULL * V0 - 2ULL * j;
}

NOINLINE LoopOut k6_appc1_chained_ghost(uint64_t L, uint64_t R) {
    uint64_t x = 2ULL;
    uint64_t k = L - 2ULL;
    uint64_t j1 = 0ULL;
    if (k >= 3ULL) {
        uint64_t U0 = 4ULL; /* x0 + 2 = 4 */
        uint64_t W1 = k + 5ULL; /* >= 2*U0 since k >= 3 */
        j1 = (uint64_t)(lzcnt64_hw(U0) - lzcnt64_hw(W1) - 1U);
        j1 += (uint64_t)(k >= k6_t1(U0, j1 + 1ULL));
        j1 += (uint64_t)(k >= k6_t1(U0, j1 + 1ULL));
        uint64_t Uj = U0 << (uint32_t)j1;
        k -= (Uj - U0) - j1;
        x = Uj - 2ULL;
    }
    uint64_t X = 2ULL * x + 2ULL;
    uint64_t z = R + 2ULL * k + 1ULL;
    uint64_t j2 = 0ULL;
    if (z >= 2ULL * X + 2ULL) {
        uint64_t V0 = X + 2ULL;
        uint64_t W2 = z + 2ULL * V0 + 2ULL; /* >= 4*V0 since z >= 2*X + 2 */
        j2 = (uint64_t)(lzcnt64_hw(V0) - lzcnt64_hw(W2) - 2U);
        j2 += (uint64_t)(z >= k6_t2(V0, j2 + 1ULL));
        j2 += (uint64_t)(z >= k6_t2(V0, j2 + 1ULL));
        uint64_t Vj = V0 << (uint32_t)j2;
        z -= 2ULL * (Vj - V0) - 2ULL * j2;
        X = Vj - 2ULL;
    }
    LoopOut out = {X, z, j1 + j2};
    return out;
}

/* ============================================================================
 * Deterministic SplitMix64 PRNG & Input Synthesis
 * ============================================================================ */

static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;

static uint64_t splitmix64(void) {
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t craft_ctz_input(uint64_t delta, uint64_t B, uint32_t v, uint32_t target_m, uint64_t seed) {
    if (target_m == 0U) {
        uint64_t z = ((seed & 0xFFFFFFULL) << 1) | 1ULL;
        if (((delta * z + B) & ((1ULL << v) - 1ULL)) == 0ULL) {
            z += 2ULL;
        }
        return z;
    }
    uint32_t bits = v * target_m;
    uint64_t mask = (1ULL << bits) - 1ULL;
    uint64_t inv = (delta == 65ULL) ? INV65_U64 : ((delta == 19ULL) ? INV19_U64 : 1ULL);
    uint64_t negB = 0ULL - B;
    uint64_t z0 = (negB * inv) & mask;
    if (z0 == 0ULL) {
        z0 += (1ULL << bits);
    }
    uint64_t q0 = (delta * z0 + B) >> bits;
    if ((q0 & 1ULL) == 0ULL) {
        z0 += (1ULL << bits);
    }
    uint64_t s = seed & 3ULL;
    return z0 + (2ULL * s << bits);
}

/* ============================================================================
 * Exhaustive & Randomized Bit-Exactness Verification Suite (1,232,500 Vectors)
 * ============================================================================ */

static void verify_all_bit_exact(void) {
    if (65ULL * INV65_U64 != 1ULL || 19ULL * INV19_U64 != 1ULL) {
        fprintf(stderr, "FATAL: Modular inverse constant mismatch!\n");
        exit(1);
    }

    uint64_t total_checks = 0ULL;

    /* 1. Verify CTZ-K1 across crafted m=0..8 and random inputs (200,000 cases; 81*z+57 < 2^64) */
    for (uint32_t i = 0; i < 200000U; ++i) {
        uint64_t s = splitmix64();
        uint32_t m_target = (uint32_t)(i % 9U);
        uint64_t z = craft_ctz_input(65ULL, 57ULL, 4U, m_target, s >> 8);
        uint64_t c = (s & 15ULL);
        LoopOut a = k1_antihydra_tneg1_naive(z, c);
        LoopOut b = k1_antihydra_tneg1_ghost(z, c);
        if (a.u != b.u || a.r != b.r || a.steps != b.steps) {
            fprintf(stderr, "MISMATCH K1 at z=%llu c=%llu\n", (unsigned long long)z, (unsigned long long)c);
            exit(1);
        }
        total_checks++;
    }

    /* 2. Verify CTZ-K2 across m=0..36 (200,000 cases; 3*z+1 < 2^64) */
    for (uint32_t i = 0; i < 200000U; ++i) {
        uint64_t s = splitmix64();
        uint32_t m_target = (uint32_t)(i % 37U);
        uint64_t z;
        if (m_target == 0U) {
            z = ((s & 0xFFFFFFFFULL) << 1);
        } else {
            uint64_t odd_mult = ((s >> 16) & 3ULL) * 2ULL + 1ULL;
            z = (odd_mult << m_target) - 1ULL;
        }
        uint64_t c = (i % 5U == 0U) ? (s % 12ULL) : 50ULL;
        LoopOut a = k2_antihydra_odd_naive(z, c);
        LoopOut b = k2_antihydra_odd_ghost(z, c);
        if (a.u != b.u || a.r != b.r || a.steps != b.steps) {
            fprintf(stderr, "MISMATCH K2 at z=%llu c=%llu\n", (unsigned long long)z, (unsigned long long)c);
            exit(1);
        }
        total_checks++;
    }

    /* 3. Verify CTZ-K3 across m=0..11 (200,000 cases; 27*z+15 < 2^64) */
    for (uint32_t i = 0; i < 200000U; ++i) {
        uint64_t s = splitmix64();
        uint32_t m_target = (uint32_t)(i % 12U);
        uint64_t z = craft_ctz_input(19ULL, 15ULL, 3U, m_target, s >> 8);
        uint64_t cap = (i % 4U == 0U) ? (s % 8ULL) : 13ULL;
        LoopOut a = k3_antihydra_t0_naive(z, cap);
        LoopOut b = k3_antihydra_t0_ghost(z, cap);
        if (a.u != b.u || a.r != b.r || a.steps != b.steps) {
            fprintf(stderr, "MISMATCH K3 at z=%llu cap=%llu\n", (unsigned long long)z, (unsigned long long)cap);
            exit(1);
        }
        total_checks++;
    }

    /* 4 & 5. Exhaustive threshold boundary sweep T(j)+delta (delta in -2..+2) for L=0..64, j=1..50 */
    for (uint64_t L = 0; L <= 64; ++L) {
        for (uint64_t j = 1; j <= 50; ++j) {
            uint64_t t4 = k4_thresh(L + 3ULL, j);
            uint64_t t5 = k5_thresh(L + 5ULL, j);
            for (int delta = -2; delta <= 2; ++delta) {
                uint64_t r4 = (delta < 0 && t4 < (uint64_t)(-delta)) ? 0ULL : (uint64_t)((int64_t)t4 + delta);
                LoopOut a4 = k4_cousin_a2_a10_naive(L, r4);
                LoopOut b4 = k4_cousin_a2_a10_ghost(L, r4);
                if (a4.u != b4.u || a4.r != b4.r || a4.steps != b4.steps) {
                    fprintf(stderr, "MISMATCH K4 boundary L=%llu r4=%llu\n",
                            (unsigned long long)L, (unsigned long long)r4);
                    exit(1);
                }
                uint64_t r5 = (delta < 0 && t5 < (uint64_t)(-delta)) ? 0ULL : (uint64_t)((int64_t)t5 + delta);
                LoopOut a5 = k5_cousin_a5_naive(L, r5);
                LoopOut b5 = k5_cousin_a5_ghost(L, r5);
                if (a5.u != b5.u || a5.r != b5.r || a5.steps != b5.steps) {
                    fprintf(stderr, "MISMATCH K5 boundary L=%llu r5=%llu\n",
                            (unsigned long long)L, (unsigned long long)r5);
                    exit(1);
                }
                total_checks += 2ULL;
            }
        }
    }

    /* 6. Random multi-scale verification for CLZ-K4, CLZ-K5, and CLZ-K6 (600,000 cases) */
    for (uint32_t i = 0; i < 200000U; ++i) {
        uint64_t s1 = splitmix64();
        uint64_t s2 = splitmix64();
        uint32_t shift = (uint32_t)(i % 56U);
        uint64_t L = s1 & 0xFFFFULL;
        uint64_t R = (s2 >> (63U - shift));
        LoopOut a4 = k4_cousin_a2_a10_naive(L, R);
        LoopOut b4 = k4_cousin_a2_a10_ghost(L, R);
        if (a4.u != b4.u || a4.r != b4.r || a4.steps != b4.steps) {
            fprintf(stderr, "MISMATCH K4 rand L=%llu R=%llu\n", (unsigned long long)L, (unsigned long long)R);
            exit(1);
        }
        LoopOut a5 = k5_cousin_a5_naive(L, R);
        LoopOut b5 = k5_cousin_a5_ghost(L, R);
        if (a5.u != b5.u || a5.r != b5.r || a5.steps != b5.steps) {
            fprintf(stderr, "MISMATCH K5 rand L=%llu R=%llu\n", (unsigned long long)L, (unsigned long long)R);
            exit(1);
        }
        uint64_t L6 = 2ULL + (s1 >> (63U - (i % 48U)));
        uint64_t R6 = (s2 >> (63U - (i % 54U)));
        LoopOut a6 = k6_appc1_chained_naive(L6, R6);
        LoopOut b6 = k6_appc1_chained_ghost(L6, R6);
        if (a6.u != b6.u || a6.r != b6.r || a6.steps != b6.steps) {
            fprintf(stderr, "MISMATCH K6 rand L=%llu R=%llu\n", (unsigned long long)L6, (unsigned long long)R6);
            exit(1);
        }
        total_checks += 3ULL;
    }

    printf("[VERIFY] 100%% bit-exact match across %llu test vectors (0 discrepancies).\n",
           (unsigned long long)total_checks);
}

/* ============================================================================
 * Benchmark Harness (Wall-Clock ns/call + RDTSC cycles/call)
 * ============================================================================ */

#define BATCH_N 65536
#define REPS    64

static uint64_t in_u[BATCH_N];
static uint64_t in_r[BATCH_N];

typedef LoopOut (*KernelFn)(uint64_t, uint64_t);

typedef struct {
    double ns_per_op;
    double cycles_per_op;
    double mean_steps;
    uint64_t checksum;
} BenchMetrics;

static BenchMetrics run_kernel_bench(KernelFn fn) {
    uint64_t sink = 0ULL;
    uint64_t step_acc = 0ULL;
    for (int i = 0; i < BATCH_N; ++i) {
        LoopOut o = fn(in_u[i], in_r[i]);
        sink ^= (o.u + (o.r << 1) + o.steps);
        step_acc += o.steps;
    }

    double best_sec = 1e30;
    uint64_t best_cycles = ~0ULL;

    for (int trial = 0; trial < 5; ++trial) {
        double t0 = now_sec();
        uint64_t c0 = read_tsc();
        for (int r = 0; r < REPS; ++r) {
            for (int i = 0; i < BATCH_N; ++i) {
                LoopOut o = fn(in_u[i], in_r[i]);
                sink ^= o.u ^ o.r ^ o.steps;
            }
        }
        uint64_t c1 = read_tsc();
        double t1 = now_sec();
        double dt = t1 - t0;
        uint64_t dc = c1 - c0;
        if (dt < best_sec) best_sec = dt;
        if (dc < best_cycles) best_cycles = dc;
    }

    double total_ops = (double)BATCH_N * (double)REPS;
    BenchMetrics m;
    m.ns_per_op = (best_sec * 1e9) / total_ops;
    m.cycles_per_op = (double)best_cycles / total_ops;
    m.mean_steps = (double)step_acc / (double)BATCH_N;
    m.checksum = sink;
    return m;
}

static void print_pair_row(const char *regime, const char *name, KernelFn naive_fn, KernelFn ghost_fn) {
    BenchMetrics mn = run_kernel_bench(naive_fn);
    BenchMetrics mg = run_kernel_bench(ghost_fn);
    if (mn.checksum != mg.checksum) {
        fprintf(stderr, "FATAL CHECKSUM MISMATCH on %s / %s!\n", regime, name);
        exit(1);
    }
    double speedup_ns = mn.ns_per_op / mg.ns_per_op;
    double speedup_cyc = mn.cycles_per_op / mg.cycles_per_op;
    printf("ROW|%s|%s|%.2f|%.3f|%.3f|%.2f|%.2f|%.2fx|%.2fx\n",
           regime, name, mn.mean_steps,
           mn.ns_per_op, mg.ns_per_op,
           mn.cycles_per_op, mg.cycles_per_op,
           speedup_ns, speedup_cyc);
}

int main(void) {
    verify_all_bit_exact();

    /* REGIME 1: Unpredictable Mixed-Scale Random Trip Counts */
    rng_state = 0x123456789ABCDEF0ULL;
    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s = splitmix64();
        uint32_t m = (uint32_t)((s % 8ULL) + 1ULL);
        in_u[i] = craft_ctz_input(65ULL, 57ULL, 4U, m, s >> 16);
        in_r[i] = 20ULL;
    }
    print_pair_row("MixedRandom", "CTZ-K1_Antihydra_Tneg1_v4", k1_antihydra_tneg1_naive, k1_antihydra_tneg1_ghost);

    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s = splitmix64();
        uint32_t m = (uint32_t)((s % 36ULL) + 1ULL);
        uint64_t odd_mult = ((s >> 16) & 3ULL) * 2ULL + 1ULL;
        in_u[i] = (odd_mult << m) - 1ULL;
        in_r[i] = 50ULL;
    }
    print_pair_row("MixedRandom", "CTZ-K2_Antihydra_OddRun_v1", k2_antihydra_odd_naive, k2_antihydra_odd_ghost);

    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s = splitmix64();
        uint32_t m = (uint32_t)((s % 11ULL) + 1ULL);
        in_u[i] = craft_ctz_input(19ULL, 15ULL, 3U, m, s >> 16);
        in_r[i] = 15ULL;
    }
    print_pair_row("MixedRandom", "CTZ-K3_Antihydra_Relay_v3", k3_antihydra_t0_naive, k3_antihydra_t0_ghost);

    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s1 = splitmix64();
        uint64_t s2 = splitmix64();
        uint32_t j_target = (uint32_t)((s1 % 48ULL) + 1ULL);
        uint64_t L = (s1 >> 16) & 255ULL;
        uint64_t lo = k4_thresh(L + 3ULL, j_target);
        uint64_t hi = k4_thresh(L + 3ULL, j_target + 1ULL);
        in_u[i] = L;
        in_r[i] = lo + (s2 % (hi - lo));
    }
    print_pair_row("MixedRandom", "CLZ-K4_Cousin_A2_A10", k4_cousin_a2_a10_naive, k4_cousin_a2_a10_ghost);

    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s1 = splitmix64();
        uint64_t s2 = splitmix64();
        uint32_t j_target = (uint32_t)((s1 % 48ULL) + 1ULL);
        uint64_t L = (s1 >> 16) & 255ULL;
        uint64_t lo = k5_thresh(L + 5ULL, j_target);
        uint64_t hi = k5_thresh(L + 5ULL, j_target + 1ULL);
        in_u[i] = L;
        in_r[i] = lo + (s2 % (hi - lo));
    }
    print_pair_row("MixedRandom", "CLZ-K5_Cousin_A5_BMO5", k5_cousin_a5_naive, k5_cousin_a5_ghost);

    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s1 = splitmix64();
        uint64_t s2 = splitmix64();
        uint32_t j1_t = (uint32_t)((s1 % 24ULL) + 1ULL);
        uint32_t j2_t = (uint32_t)((s2 % 24ULL) + 1ULL);
        in_u[i] = 2ULL + k6_t1(4ULL, j1_t) + ((s1 >> 20) & 7ULL);
        in_r[i] = (1ULL << (j1_t + j2_t + 3U)) + ((s2 >> 20) & 1023ULL);
    }
    print_pair_row("MixedRandom", "CLZ-K6_AppC1_Chained2Loop", k6_appc1_chained_naive, k6_appc1_chained_ghost);

    /* REGIME 2: Geometric / Realistic 2-Adic & Short-Epoch Distribution */
    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s = splitmix64();
        uint32_t m = ctz64_hw(s | (1ULL << 35)) + 1U;
        uint64_t odd_mult = ((s >> 40) & 3ULL) * 2ULL + 1ULL;
        in_u[i] = (odd_mult << m) - 1ULL;
        in_r[i] = 50ULL;
    }
    print_pair_row("Geom2Adic", "CTZ-K2_Geom_Half", k2_antihydra_odd_naive, k2_antihydra_odd_ghost);

    for (int i = 0; i < BATCH_N; ++i) {
        uint64_t s1 = splitmix64();
        uint64_t s2 = splitmix64();
        uint32_t j_target = (uint32_t)((s1 & 15ULL) + 1ULL);
        uint64_t L = (s1 >> 16) & 63ULL;
        uint64_t lo = k5_thresh(L + 5ULL, j_target);
        uint64_t hi = k5_thresh(L + 5ULL, j_target + 1ULL);
        in_u[i] = L;
        in_r[i] = lo + (s2 % (hi - lo));
    }
    print_pair_row("ShortEpoch_1_16", "CLZ-K5_ShortEpoch", k5_cousin_a5_naive, k5_cousin_a5_ghost);

    /* REGIME 3: Asymptotic Trip-Depth Scaling Sweep on CLZ-K5 (j = 1..48) */
    const uint32_t depths[7] = {1U, 2U, 4U, 8U, 16U, 32U, 48U};
    for (int d_idx = 0; d_idx < 7; ++d_idx) {
        uint32_t j_fixed = depths[d_idx];
        char label[64];
        snprintf(label, sizeof(label), "CLZ-K5_Depth_j=%u", j_fixed);
        for (int i = 0; i < BATCH_N; ++i) {
            uint64_t s1 = splitmix64();
            uint64_t s2 = splitmix64();
            uint64_t L = (s1 >> 16) & 255ULL;
            uint64_t lo = k5_thresh(L + 5ULL, j_fixed);
            uint64_t hi = k5_thresh(L + 5ULL, j_fixed + 1ULL);
            in_u[i] = L;
            in_r[i] = lo + (s2 % (hi - lo));
        }
        print_pair_row("DepthSweep", label, k5_cousin_a5_naive, k5_cousin_a5_ghost);
    }

    return 0;
}
