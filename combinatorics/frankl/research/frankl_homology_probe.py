#!/usr/bin/env python3
"""Full homology of the order complex of the proper part of a finite lattice,
and its relation to Frankl-tightness (lattice form).

The order complex Δ((⊥,⊤)) has the chains of the proper part L∖{⊥,⊤} as its
simplices.  Its reduced Euler characteristic equals μ(⊥,⊤) (Philip Hall) — this
is checked as a sanity test.  We compute reduced Betti numbers over GF(2) and
correlate the homotopy type with the Frankl margin (n/2 − min_j |↑j|).

Findings (2026-05-28), exhaustive on B_4 (verified: Euler == μ for all 2479):

  * tight (extremal, 2·min|↑j| = |L|) lattices are exactly homotopy SPHERES:
    reduced Betti = (), (1), (0,1), (0,0,1), … — a single 1 in top degree
    (like the Boolean lattice, whose proper part is a sphere).
  * NON-spherical order complex (acyclic, or higher/multiple reduced homology)
    ⟹ strict Frankl slack.  This strictly refines "μ=0 ⟹ slack" (it now also
    catches μ≠0-but-non-spherical lattices like reduced Betti (2,), (1,1)).
  * BUT spherical does NOT imply tight: S¹ etc. occur among slack lattices too
    (B_4: 97 spherical-tight vs 668 spherical-slack).  So homology narrows the
    hard cases to "spheres" but the final tight/slack cut is invisible to it —
    the non-locality persists at the finest topological resolution.
"""
from __future__ import annotations
import random
from itertools import combinations

popcount = lambda x: bin(x).count("1")


def gf2_rank(rows):
    rank, piv = 0, {}
    for r in rows:
        cur = r
        while cur:
            hb = cur.bit_length() - 1
            if hb in piv:
                cur ^= piv[hb]
            else:
                piv[hb] = cur; rank += 1; break
    return rank


def order_complex_betti(L):
    """Reduced GF(2) Betti vector of Δ((⊥,⊤)) for a closure-system lattice L
    (a sorted list of subset-bitmasks, meet = &)."""
    bot = min(L, key=popcount); top = max(L, key=popcount)
    P = [x for x in L if x != bot and x != top]; n = len(P)
    leq = lambda a, b: (a & b) == a
    comp = [[(leq(P[i], P[j]) or leq(P[j], P[i])) for j in range(n)] for i in range(n)]
    cbs = {}
    for sub in range(1, 1 << n):
        e = [i for i in range(n) if sub >> i & 1]
        if all(comp[a][b] for a, b in combinations(e, 2)):
            cbs.setdefault(len(e), []).append(tuple(e))
    si = {sz: {c: i for i, c in enumerate(cl)} for sz, cl in cbs.items()}

    def brank(s):
        if s not in si or (s - 1) not in si:
            return 0
        tgt = si[s - 1]; rows = []
        for c in si[s]:
            row = 0
            for i in range(len(c)):
                row ^= 1 << tgt[c[:i] + c[i + 1:]]
            rows.append(row)
        return gf2_rank(rows)

    sizes = sorted(cbs); dimC = {s: len(cbs[s]) for s in sizes}
    rk = {s: brank(s) for s in sizes if s >= 2}
    maxk = max(sizes) if sizes else 0
    betti = [dimC.get(k + 1, 0) - rk.get(k + 1, 0) - rk.get(k + 2, 0) for k in range(maxk)]
    if betti:
        betti[0] -= 1                                  # reduce H_0
    reduced_euler = -1 + sum(((-1) ** (s - 1)) * dimC[s] for s in sizes)
    return betti, reduced_euler


def mu_bot_top(L):
    L = sorted(L, key=popcount); n = len(L); bot = L[0]
    leq = lambda a, b: (a & b) == a
    order = sorted(range(n), key=lambda y: sum(leq(L[z], L[y]) for z in range(n)))
    mub = [0] * n
    for y in order:
        if L[y] == bot:
            mub[y] = 1
        elif not leq(bot, L[y]):
            mub[y] = 0
        else:
            mub[y] = -sum(mub[z] for z in range(n) if leq(bot, L[z]) and leq(L[z], L[y]) and z != y)
    return mub[n - 1]


def margin(L):
    L = sorted(L, key=popcount); n = len(L); bot = L[0]
    leq = lambda a, b: (a & b) == a

    def join(a, b):
        u = a | b
        return min((c for c in L if (u & c) == u), key=popcount)
    JI = [x for x in L if x != bot and not any(
        join(a, b) == x for a in L if leq(a, x) and a != x for b in L if leq(b, x) and b != x)]
    up = lambda x: sum(1 for y in L if leq(x, y))
    return min(up(j) for j in JI), n


def is_sphere(betti):
    if len(betti) == 0:
        return True
    nz = [(i, v) for i, v in enumerate(betti) if v != 0]
    return len(nz) == 1 and nz[0][1] == 1


def lattices_on(k):
    U = (1 << k) - 1; others = [s for s in range(1 << k) if s != U]; res = set()
    for bits in range(1 << len(others)):
        fam = {U}
        for i, s in enumerate(others):
            if bits >> i & 1:
                fam.add(s)
        if len(fam) >= 2 and all((a & b) in fam for a in fam for b in fam):
            res.add(frozenset(fam))
    return res


if __name__ == "__main__":
    import collections
    allL = lattices_on(4)
    euler_ok = nonsph_tight = sph_tight = sph_slack = 0
    tight_b = collections.Counter()
    for fam in allL:
        b, eul = order_complex_betti(fam)
        euler_ok += (eul == mu_bot_top(fam))
        mn, n = margin(fam); tight = (2 * mn == n); sph = is_sphere(b)
        if tight:
            tight_b[tuple(b)] += 1
        if tight and not sph:
            nonsph_tight += 1
        if tight and sph:
            sph_tight += 1
        if (not tight) and sph:
            sph_slack += 1
    print(f"B_4: {len(allL)} lattices | sanity (reduced Euler == μ): {euler_ok}/{len(allL)}")
    print(f"  tight Betti vectors (all spheres): {dict(tight_b)}")
    print(f"  non-spherical & tight (must be 0): {nonsph_tight}")
    print(f"  spherical & tight = {sph_tight}; spherical & slack = {sph_slack}")
    print(f"  => non-spherical ⟹ slack: {nonsph_tight == 0}; spheres include slack: {sph_slack > 0}")
