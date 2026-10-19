#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
/* For each prime p < N: s = !p mod p = sum_{j<p} j! mod p.
   Report p with p | !p - !k for k = 0..8 (p > k). */
int main(int argc, char **argv) {
    long N = argc > 1 ? atol(argv[1]) : 1000000;
    char *comp = calloc(N + 1, 1);
    for (long i = 2; i * i <= N; i++) if (!comp[i]) for (long j = i * i; j <= N; j += i) comp[j] = 1;
    long lf[9]; lf[0] = 0; { long f = 1; for (int k = 1; k < 9; k++) { lf[k] = lf[k-1] + f; f *= k; } }
    for (long p = 3; p <= N; p++) {
        if (comp[p]) continue;
        uint64_t s = 0, f = 1;
        for (uint64_t j = 0; j < (uint64_t)p; j++) { if (j) f = f * j % p; s += f; if (s >= (uint64_t)p) s -= p; }
        for (int k = 0; k < 9; k++) if (p > k && (s + p - (uint64_t)(lf[k] % p)) % p == 0) printf("%d %ld\n", k, p);
    }
    return 0;
}
