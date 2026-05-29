#!/usr/bin/env python3
"""Conjecture `tight ⟺ Boolean` for the lattice form of Frankl, with the
verified reduction.  See `frankl_tight_boolean.md`.

  tight   := min over join-irreducibles j of |↑j| = |L|/2  (Frankl-extremal)
  all-half := every join-irreducible j has |↑j| = |L|/2

Checks (closure-system lattices, meet = ∩):
  * tight ⟺ Boolean      (exhaustive on B_4; sampled larger)
  * all-half ⟹ Boolean   (the crux statement: every atom in exactly half the
                           closed sets ⟹ power set)
  * all-half ⟹ join-irreducibles are atoms   (a PROVED lemma — sanity check)

Status: conjecture with partial proof; the steps `tight ⟹ all-half` and
`all-half ⟹ distributive` are open (see the .md).
"""
from __future__ import annotations
import random

popcount = lambda x: bin(x).count("1")


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


def close_inter(gens, k):
    U = (1 << k) - 1; fam = set(gens) | {U}; ch = True
    while ch:
        ch = False
        for a in list(fam):
            for b in list(fam):
                if (a & b) not in fam:
                    fam.add(a & b); ch = True
    return frozenset(fam)


def analyze(fam):
    fam = sorted(fam, key=popcount); n = len(fam); bot = fam[0]; top = fam[-1]
    leq = lambda a, b: (a & b) == a

    def join(a, b):
        u = a | b
        return min((c for c in fam if (u & c) == u), key=popcount)
    meet = lambda a, b: a & b
    JI = [x for x in fam if x != bot and not any(
        join(a, b) == x for a in fam if leq(a, x) and a != x for b in fam if leq(b, x) and b != x)]
    atoms = [x for x in fam if x != bot and leq(bot, x) and not any(
        leq(bot, z) and leq(z, x) and z != bot and z != x for z in fam)]
    up = lambda x: sum(1 for y in fam if leq(x, y))
    minup = min(up(j) for j in JI)
    tight = (2 * minup == n)
    allhalf = all(2 * up(j) == n for j in JI)
    distributive = all(meet(a, join(b, c)) == join(meet(a, b), meet(a, c))
                       for a in fam for b in fam for c in fam)
    complemented = all(any(meet(a, ap) == bot and join(a, ap) == top for ap in fam) for a in fam)
    boolean = distributive and complemented
    ji_are_atoms = set(JI) == set(atoms)
    return dict(tight=tight, allhalf=allhalf, boolean=boolean,
                distributive=distributive, ji_are_atoms=ji_are_atoms)


if __name__ == "__main__":
    allL = lattices_on(4)
    t = tnb = ah = ahnb = ah_not_jiatoms = 0
    for fam in allL:
        d = analyze(fam)
        if d["tight"]:
            t += 1
            if not d["boolean"]:
                tnb += 1
        if d["allhalf"]:
            ah += 1
            if not d["boolean"]:
                ahnb += 1
            if not d["ji_are_atoms"]:
                ah_not_jiatoms += 1
    print(f"B_4 exhaustive ({len(allL)} lattices):")
    print(f"  tight={t}, tight-but-NOT-Boolean={tnb}")
    print(f"  all-half={ah}, all-half-but-NOT-Boolean={ahnb}")
    print(f"  all-half-but-NOT(ji-are-atoms)={ah_not_jiatoms}  (proved lemma: must be 0)")

    random.seed(0)
    t = tnb = 0
    for _ in range(120000):
        k = random.choice([5, 6, 7, 8])
        fam = close_inter([random.randint(0, (1 << k) - 1) for _ in range(random.randint(2, 2 * k))], k)
        if len(fam) < 2:
            continue
        d = analyze(fam)
        if d["tight"]:
            t += 1
            if not d["boolean"]:
                tnb += 1
    print(f"sampled [5]-[8]: tight={t}, tight-but-NOT-Boolean={tnb}")
