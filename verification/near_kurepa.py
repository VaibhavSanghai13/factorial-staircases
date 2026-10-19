"""Near-Kurepa primes (paper Table 'near-Kurepa primes' and the 11563 remark).

Lists the odd primes p < LIMIT with p | !p - !k for k = 0..6, where !n = 0! + 1! + ... + (n-1)!.
Pure Python; takes a few minutes for LIMIT = 30000.
"""
from math import factorial

LIMIT = 30000


def primes_below(n):
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n) if sieve[i]]


left = [sum(factorial(j) for j in range(k)) for k in range(7)]   # !0 .. !6
hits = {k: [] for k in range(7)}
for p in primes_below(LIMIT)[1:]:     # odd primes only
    s, f = 0, 1
    for j in range(p):            # s = !p mod p
        if j:
            f = f * j % p
        s = (s + f) % p
    for k in hits:
        if p > k and (s - left[k]) % p == 0:
            hits[k].append(p)
for k, ps in hits.items():
    print(f"k={k} (!k={left[k]}): {ps}")

# Mestrovic's counterexample 11563 = 31 * 373: check d_{n-1} = 2 (mod n).
n, d = 31 * 373, 1
for k in range(1, n):
    d = (k * d + (-1) ** k) % n
print("d_11562 mod 11563 =", d)
