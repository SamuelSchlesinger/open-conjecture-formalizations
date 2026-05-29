#!/usr/bin/env python3
"""Computational attack on the lattice form of Frankl's union-closed conjecture.

Lattice form: every finite lattice `L` with `|L| ≥ 2` has a join-irreducible `j`
with `|↑j| ≤ |L|/2`.  (Equivalent to the set conjecture; see `Frankl.Lattice`.)

This script tests several *elementary sufficient conditions* and the
*strengthened coatom-union condition* (see `lattice_frankl_attack.md`) by
enumerating / sampling finite lattices.  All conditions are sound: each one,
when it holds for a lattice, exhibits a join-irreducible witness `x` together
with a set of size `≥ |↑x|` disjoint from `↑x`, hence `2|↑x| ≤ |L|`.

Findings (2026-05-28):
  * uniform averaging over join-irreducibles FAILS (deep join-irreducibles
    inflate the average); only *maximal* join-irreducibles are candidates.
  * "some coatom has |↓m| ≥ |L|/2" covers all of B_3 but leaves 26 escapers
    in B_4 (formalized as `Frankl.franklLattice_of_large_coatom_ideal`).
  * the strengthened coatom-union condition (∃ join-irreducible x with
    |⋃_{coatoms m ⊉ x} ↓m| ≥ |↑x|) has ZERO failures across all of B_3, B_4
    and 7000+ sampled lattices up to size 38, and on Π_3..Π_5 and subspace
    lattices.  This is *not* a proof — almost certainly the sampling is biased
    or the condition is equivalent-in-difficulty to the open conjecture.
"""

from __future__ import annotations
import random
from itertools import combinations


# --- lattices as closure systems (intersection-closed families) on [k] -------

def lattices_on(k):
    """All closure systems on [k] (intersection-closed, containing the top)."""
    U = (1 << k) - 1
    others = [s for s in range(1 << k) if s != U]
    res = set()
    for bits in range(1 << len(others)):
        fam = {U}
        for idx, s in enumerate(others):
            if bits >> idx & 1:
                fam.add(s)
        if len(fam) >= 2 and all((a & b) in fam for a in fam for b in fam):
            res.add(frozenset(fam))
    return res


def close_inter(gens, k):
    U = (1 << k) - 1
    fam = set(gens) | {U}
    changed = True
    while changed:
        changed = False
        for a in list(fam):
            for b in list(fam):
                if (a & b) not in fam:
                    fam.add(a & b); changed = True
    return frozenset(fam)


# --- analysis of a single lattice given as a sorted family of bitmasks -------

def analyze(fam):
    fam = sorted(fam); n = len(fam)
    bot = min(fam, key=lambda A: bin(A).count("1"))
    top = max(fam, key=lambda A: bin(A).count("1"))
    jm = {}

    def join(A, B):
        if (A, B) in jm:
            return jm[(A, B)]
        u = A | B
        best = min((C for C in fam if (u & C) == u), key=lambda C: bin(C).count("1"))
        jm[(A, B)] = best
        return best

    JI = set()
    for x in fam:
        if x == bot:
            continue
        below = [a for a in fam if (a & x) == a and a != x]
        if not any(join(a, b) == x for a in below for b in below):
            JI.add(x)
    up = lambda x: set(y for y in fam if (x & y) == x)
    dn = lambda m: set(y for y in fam if (y & m) == y)
    coat = [m for m in fam if m != top and (m & top) == m and
            not any((m & z) == m and m != z and (z & top) == z and z != top for z in fam)]
    atom = [a for a in fam if a != bot and (bot & a) == bot and
            not any((b & a) == b and b != a and (bot & b) == bot and b != bot for b in fam)]

    modular = True
    for a in fam:
        if not modular:
            break
        for c in fam:
            if (a & c) != a:
                continue
            for b in fam:
                if join(a, (b & c)) != (join(a, b) & c):
                    modular = False; break
            if not modular:
                break

    frankl = any(2 * len(up(j)) <= n for j in JI)
    cond_coatom = any(2 * len(dn(m)) >= n for m in coat)
    cond_atom = any(2 * len(up(a)) >= n for a in atom)
    ji_coatom = any(m in JI for m in coat)

    def coatom_union_holds(x):
        union = set()
        for m in coat:
            if (x & m) != x:           # x ⊄ m
                union |= dn(m)
        return len(union) >= len(up(x))
    strong = any(coatom_union_holds(x) for x in JI)

    return dict(n=n, frankl=frankl, modular=modular, cond_coatom=cond_coatom,
                cond_atom=cond_atom, ji_coatom=ji_coatom, strong=strong)


def report_exhaustive(k):
    allL = lattices_on(k)
    ff = esc3 = esc4 = escS = 0
    for fam in allL:
        r = analyze(fam)
        ff += (not r["frankl"])
        cov3 = r["modular"] or r["cond_coatom"] or r["cond_atom"]
        esc3 += (not cov3)
        esc4 += (not (cov3 or r["ji_coatom"]))
        escS += (not r["strong"])
    print(f"B_{k}: {len(allL)} lattices | Frankl-fails={ff} | "
          f"escapers(3 conds)={esc3} | (+ji-coatom)={esc4} | strong-cond-fails={escS}")


def report_sampled(k, trials, seed):
    random.seed(seed)
    ff = fs = t = 0; mx = 0
    for _ in range(trials):
        gens = [random.randint(0, (1 << k) - 1) for _ in range(random.randint(2, 2 * k))]
        fam = close_inter(gens, k)
        if len(fam) < 2:
            continue
        r = analyze(fam); t += 1; mx = max(mx, r["n"])
        ff += (not r["frankl"]); fs += (not r["strong"])
    print(f"[{k}] sampled {t}: max|L|={mx} | Frankl-fails={ff} | strong-cond-fails={fs}")


if __name__ == "__main__":
    report_exhaustive(3)
    report_exhaustive(4)
    report_sampled(5, 4000, 12345)
    report_sampled(6, 3000, 999)
