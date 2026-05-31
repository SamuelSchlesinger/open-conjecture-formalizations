#!/usr/bin/env python3
"""
Computational exploration of Singmaster's conjecture.

N(a) = number of positions (n,k), 0<=k<=n, with C(n,k) = a  (the multiplicity).

We compute N(a) for every a in [2, L] exactly, by sweeping Pascal's triangle:
for each row n and 1 <= k <= n//2 we add 1 (if k == n-k) or 2 (the symmetric
pair) to the tally of C(n,k), stopping each row once the binomial exceeds L.
Every occurrence of a value <= L is counted exactly once.

Outputs: the multiplicity distribution, the maximum multiplicity in range, and
the lists of numbers attaining 6 and 8 (the conjectured record).
"""
from collections import Counter
from math import comb, isqrt

def multiplicities(L):
    """tally[a] = N(a) for 2 <= a <= L."""
    tally = Counter()
    # k = 1 column: C(n,1) = n and C(n,n-1) = n for every n in [2, L].
    for n in range(2, L + 1):
        tally[n] += 1                 # (n, 1)
        if n - 1 != 1:                # (n, n-1) distinct from (n,1) iff n != 2
            tally[n] += 1
    # k >= 2 (interior); C(n,2) <= L forces n <= ~sqrt(2L), so this is cheap.
    n = 2
    while comb(n, 2) <= L:
        k = 2
        while k <= n - k:             # k <= n//2
            c = comb(n, k)
            if c > L:
                break
            if k == n - k:
                tally[c] += 1
            else:
                tally[c] += 2
            k += 1
        n += 1
    return tally

def report(L):
    print("=" * 66)
    print(f"Singmaster multiplicities for a in [2, {L}]")
    print("=" * 66)
    tally = multiplicities(L)
    dist = Counter(tally.values())
    print("multiplicity m : #{a in [2,L] : N(a) = m}")
    for m in sorted(dist):
        print(f"  N(a) = {m:2d} : {dist[m]} values")
    mx = max(tally.values())
    print(f"max multiplicity in range = {mx}")
    six = sorted(a for a, m in tally.items() if m == 6)
    eight = sorted(a for a, m in tally.items() if m >= 8)
    print(f"appear exactly 6 times ({len(six)}): {six[:20]}{' ...' if len(six)>20 else ''}")
    print(f"appear >= 8 times ({len(eight)}): {eight}")
    # sanity: the proved facts
    print("--- sanity vs Lean theorems ---")
    print(f"N(2)={tally[2]}, N(6)={tally[6]}, N(10)={tally[10]} (Lean: 1,3,4)")
    print(f"min over a>=3 of N(a) = {min(m for a,m in tally.items() if a>=3)} (Lean: >=2)")
    cnt2 = [comb(n,2) for n in range(5, 60)]
    print(f"C(n,2), n in [5,59]: min N = {min(tally[c] for c in cnt2)} (Lean: >=4)")

if __name__ == "__main__":
    report(10**6)
