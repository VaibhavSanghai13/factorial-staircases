"""Computer checks for "Factorial staircases" (paper/main.tex).

Run:  python3 verify.py      (needs sympy and mpmath)
Each block prints True when its check passes. Labels refer to main.tex.
"""
from math import factorial as F
from itertools import permutations
import sympy as sp

# 1. Staircase identity (thm:identity): n! - (n-m)*sum_{i=1}^{m+1}(n-i)!  ==  sum_{i=1}^{m-1}(m-i)(n-i)!
ok=True
for n in range(2,40):
    for m in range(0,n):
        D = F(n) - (n-m)*sum(F(n-i) for i in range(1,m+2))
        R = sum((m-i)*F(n-i) for i in range(1,m))
        ok &= (D==R) and D>=0
print("core identity, n<40, all 0<=m<=n-1:", ok)

# 2. Rank of the prefix reversal (lem:rank, thm:lex)
def lex_rank(w):
    n=len(w); r=0
    for i in range(n):
        r += sum(1 for j in range(i+1,n) if w[j]<w[i]) * F(n-1-i)
    return r
ok=True
for n in range(1,10):
    for m in range(0,n):
        w = list(range(m,0,-1))+list(range(m+1,n+1))
        D = F(n) - (n-m)*sum(F(n-i) for i in range(1,m+2))
        ok &= lex_rank(w)==D
        # brute force count of perms >= w
        if n<=7:
            cnt = sum(1 for p in permutations(range(1,n+1)) if list(p)>=w)
            ok &= cnt==(n-m)*sum(F(n-i) for i in range(1,m+2))
print("rank of prefix-reversal == remainder (brute force n<=7):", ok)

# 2b. Other reversals and colex order (rem:other)
ok=True
for n in range(1,8):
    P=list(permutations(range(1,n+1)))
    lex={p:i for i,p in enumerate(sorted(P))}
    colex={p:i for i,p in enumerate(sorted(P,key=lambda p:p[::-1]))}
    L=lambda m: sum(F(n-i) for i in range(1,m+2))
    for m in range(0,n+1):
        w=tuple(list(range(m,0,-1))+list(range(m+1,n+1)))        # prefix reversal
        v=tuple(list(range(1,n-m+1))+list(range(n,n-m,-1)))      # suffix reversal
        ok &= lex[v]==F(m)-1                                      # (1)
        ok &= colex[w]==F(n)-F(m)                                 # (3), prefix
        if m<=n-1:
            ok &= colex[v]==(n-m)*L(m)-1                          # (3), suffix
            ok &= F(n)-1-colex[v]==F(n)-(n-m)*L(m)                # R_m(n) after v_m
        for a in range(0,n-m+1):                                  # (2), middle block
            b=tuple(list(range(1,a+1))+list(range(a+m,a,-1))+list(range(a+m+1,n+1)))
            k=n-a
            ok &= lex[b]==(F(k)-(k-m)*sum(F(k-i) for i in range(1,m+2)) if m<=k-1 else F(m)-1)
print("other reversals and colex order (n<=7):", ok)

# 3. Other multipliers, permutation w_{m,c} (thm:family)
ok=True
for n in range(2,9):
    for m in range(0,n):
        for c in range(1,n-m+1):
            w = list(range(n-c, n-c-m, -1)) + [n-c+1] + list(range(1,n-c-m+1)) + list(range(n-c+2,n+1))
            assert sorted(w)==list(range(1,n+1)), (n,m,c,w)
            ok &= F(n)-lex_rank(w) == c*sum(F(n-i) for i in range(1,m+2))
print("two-parameter family (m,c):", ok)

# 4. q-analogue by inversions (thm:q)
q=sp.symbols('q')
def qint(k): return sum(q**j for j in range(k))
def qfac(k):
    r=sp.Integer(1)
    for j in range(1,k+1): r*=qint(j)
    return sp.expand(r)
ok=True
for n in range(1,8):
    for m in range(0,n):
        e=lambda i: sum(m-j for j in range(1,i))
        lhs=qfac(n)
        rhs=sum(q**e(i)*qfac(n-i)*(qint(m-i)+q**(m-i+1)*qint(n-m)) for i in range(1,m+1)) + q**e(m+1)*qfac(n-m)
        ok &= sp.expand(lhs-rhs)==0
        # q-count of perms >= w by inversions
        if n<=6:
            w = list(range(m,0,-1))+list(range(m+1,n+1))
            inv=lambda p: sum(1 for a in range(n) for b in range(a+1,n) if p[a]>p[b])
            above=sum(q**inv(p) for p in permutations(range(1,n+1)) if list(p)>=w)
            pred=sum(q**e(i)*qfac(n-i)*q**(m-i+1)*qint(n-m) for i in range(1,m+1)) + q**e(m+1)*qfac(n-m)
            ok &= sp.expand(above-pred)==0
print("q-analogue:", ok)

# 5. Gamma version at non-integer x (remark prop:gamma)
import mpmath as mp; mp.mp.dps = 60
ok=True
for x in [mp.mpf('7.3'), mp.mpf('12.5'), mp.mpf('20.123'), mp.mpc('9.5','2.25')]:
    for m in range(0,5):
        lhs=mp.gamma(x+1); rhs=(x-m)*sum(mp.gamma(x-i+1) for i in range(1,m+2)) + sum((m-i)*mp.gamma(x-i+1) for i in range(1,m))
        ok &= abs(lhs-rhs)/abs(lhs) < 1e-40
print("Gamma extension:", ok)

# 5b. Mixed-radix version (thm:mixed, remark cor:affine, tab:mixed)
import random
from itertools import product
from math import prod
def mixed_ok(r, n, m):
    """r[1..n] are growth factors (r[0] unused); a_k = r_1 ... r_k."""
    a = [prod(r[1:k+1]) for k in range(n+1)]
    c = r[n-m]
    t = [r[n-i+1]-c-1 for i in range(1, m+1)]
    ok = a[n] == c*sum(a[n-i] for i in range(1, m+2)) + sum(t[i-1]*a[n-i] for i in range(1, m+1))
    if all(x >= 0 for x in t) and a[n] <= 50000:   # enumerate W_n in lexicographic order
        strings = sorted(product(*[range(r[n-i+1]) for i in range(1, n+1)]))
        s = tuple(t + [0]*(n-m))
        ok &= strings.index(s) == sum(t[i-1]*a[n-i] for i in range(1, m+1))
        ok &= sum(1 for e in strings if e >= s) == c*sum(a[n-i] for i in range(1, m+2))
    return ok, t
random.seed(1)
ok = True
for _ in range(400):
    n = random.randint(2, 7); m = random.randint(0, n-1)
    ok &= mixed_ok([None] + sorted(random.randint(1, 6) for _ in range(n)), n, m)[0]
print("mixed-radix theorem (random growth factors):", ok)
for name, rf, alpha in [("n!", lambda k: k, 1), ("(2n)!!", lambda k: 2*k, 2),
                        ("(2n-1)!!", lambda k: 2*k-1, 2), ("prod(3k-2)", lambda k: 3*k-2, 3)]:
    good = True
    for n in range(2, 9):
        for m in range(0, n):
            okk, t = mixed_ok([None] + [rf(k) for k in range(1, n+1)], n, m)
            good &= okk and t == [alpha*(m-i+1)-1 for i in range(1, m+1)]
    print(f"  equally spaced staircase for {name} (alpha={alpha}):", good)
print("  double factorial example 384 = 4(48+8+2)+3*48+1*8:", 384 == 4*(48+8+2)+3*48+1*8)
print("  walk example n=5,m=3: above=66, below=54:",
      sum(1 for p in permutations(range(1,6)) if list(p) >= [3,2,1,4,5]) == 66 == 2*(24+6+2+1),
      F(5)-66 == 54 == 2*24+6)

# 5c. Congruences modulo primes (thm:period, cor:kellner, cor:gcd)
from math import gcd
from sympy import primerange, factorint
def der(j):
    d = [1, 0]
    for k in range(2, j+1): d.append((k-1)*(d[-1]+d[-2]))
    return d[j]
def falling(j, k):
    r = 1
    for t in range(k): r *= j-t
    return r
Lb = lambda m, n: sum(F(n-i) for i in range(1, m+2))
Pc = lambda m, n: Lb(m, n)//F(n-m-1)
ok = True; cases = 0
for p in primerange(2, 30):
    for n in range(1, 60):
        for m in range(0, n):
            j = (m-n) % p
            ok &= (Pc(m, n) - sum((-1)**k*falling(j, k) for k in range(min(m, j)+1))) % p == 0
            if j <= m: ok &= (Pc(m, n) - (-1)**j*der(j)) % p == 0
            cases += 1
print(f"periodicity theorem mod p ({cases} cases):", ok)
ok = all((Lb(m, p) + der(m)*pow(F(m), -1, p)) % p == 0 for p in primerange(3, 80) for m in range(p))
print("Kellner's congruence L_m(p) = -d_m/m! (p<80):", ok)
ok = True
for n in range(2, 60):
    for m in range(0, n):
        G = gcd(Lb(m, n), F(n))//F(n-m-1)
        for p in primerange(2, n+1):
            window = any(x % p == 0 for x in range(n-m, n+1))
            ok &= (G % p == 0) == (window and Pc(m, n) % p == 0)
        ok &= all(q <= n for q in factorint(G))
        if m >= 1: ok &= G % (n-m+1) == 0
print("primes shared with n! (gcd corollary, n<60):", ok)

# 5d. Exact power of p on the diagonal p | n-m+1 (prop:val) and Hensel (rem:hensel)
def vp(p, N):
    k = 0
    while N % p == 0: N //= p; k += 1
    return k
def Pr(m, n):                          # P_m(n) = sum_k a^(rising k), a = n-m (no big factorials)
    a = n - m; s = 0; t = 1
    for k in range(m+1): s += t; t *= a + k
    return s
ok = all(Pr(m, n) == Pc(m, n) for n in range(2, 40) for m in range(n))
cases = 0
for p in primerange(2, 40):
    for m in range(2, 35):
        A = sum(F(k) for k in range(1, m-1))
        for n in range(m+1, m+1+3*p**3):
            if (n-m+1) % p: continue
            cases += 1
            if A % p: ok &= vp(p, Pr(m, n)) == vp(p, n-m+1)
            else:     ok &= vp(p, Pr(m, n)) >  vp(p, n-m+1)
        if m >= p+1: ok &= (A % p == 0) == ((sum(F(k) for k in range(p)) - 1) % p == 0)
print(f"exact power on the diagonal p | n-m+1 ({cases} cases):", ok)
def f_coeffs(m):                       # f_m(x) = sum_k x^(rising k), low degree first
    c = [0]*(m+1); t = [1]
    for k in range(m+1):
        for i, a in enumerate(t): c[i] += a
        nt = [0]*(len(t)+1)
        for i, a in enumerate(t): nt[i] += a*k; nt[i+1] += a
        t = nt
    return c
ev = lambda c, a, M: sum(ci*pow(a, i, M) for i, ci in enumerate(c)) % M
simple = nonsimple = 0; ok = True
for p in primerange(3, 40):
    for m in range(2, 40):
        c = f_coeffs(m); d = [i*ci for i, ci in enumerate(c)][1:]
        for a0 in range(p-1):                       # roots other than a = -1
            if ev(c, a0, p): continue
            if ev(d, a0, p) == 0: nonsimple += 1; continue
            simple += 1
            E = 8; M = p**E; al = a0
            for _ in range(E): al = (al - ev(c, al, M)*pow(ev(d, al, M), -1, M)) % M
            for a in range(a0, a0 + p**3, p):
                val = vp(p, sum(ci*a**i for i, ci in enumerate(c)))
                ok &= val >= E or val == min(vp(p, (a-al) % M or M), E)
print(f"Hensel: {simple} simple and {nonsimple} non-simple roots; v_p = v_p(a - alpha) at simple roots:", ok)
