#!/usr/bin/env python3
"""Set-side data-mining: structural rules that pick an abundant element.

A *rule* `R(F)` selects elements from the shape of a union-closed family `F`
(not from frequency directly).  We test whether `R(F)` always contains an
*abundant* element (one in ≥ |F|/2 members) — i.e. whether the rule is a valid
"Frankl witness selector".  Any such rule, if always valid, would imply Frankl;
so an always-valid rule is conjecture-equivalent (for *proving*).  But these
rules are also *strictly stronger* than Frankl, hence falsifiable: a family
where the rule misses every abundant element disproves the rule.

Two rules survive everything tested (2026-05-28):

  minmember : some element of a minimum-size nonempty member is abundant.
              (For min size ≤ 2 this is exactly the singleton/doubleton cases
              proved in `Frankl.Basic`; for min size ≥ 3 it is open.)
  invsize   : the element maximizing  Σ_{A ∋ x} 1/|A|  is abundant.
              (= the most likely element under "pick a random member, then a
              random element of it".)

Evidence: zero failures over all 120 families on [3], all 4958 on [4], and
~150k sampled families on [5]–[8] including adversarial min-size-≥3,
min-size-≥4, and "rare-block" constructions.  This is NOT a proof; like the
lattice-side condition (★), these appear conjecture-equivalent.
"""

from __future__ import annotations
import random
from itertools import combinations

popcount = lambda x: bin(x).count("1")


def close_union(gens):
    fam = set(gens)
    changed = True
    while changed:
        changed = False
        for a in list(fam):
            for b in list(fam):
                if (a | b) not in fam:
                    fam.add(a | b); changed = True
    return fam


def abundant(fam, n):
    L = len(fam)
    return set(x for x in range(n) if 2 * sum(1 for A in fam if A >> x & 1) >= L)


def rule_minmember(fam, n):
    nz = [A for A in fam if A != 0]
    if not nz:
        return set()
    ms = min(popcount(A) for A in nz)
    sel = set()
    for A in nz:
        if popcount(A) == ms:
            sel |= {x for x in range(n) if A >> x & 1}
    return sel


def rule_invsize(fam, n):
    sc = [0.0] * n
    for A in fam:
        if A == 0:
            continue
        for x in range(n):
            if A >> x & 1:
                sc[x] += 1.0 / popcount(A)
    m = max(sc) if any(sc) else 0.0
    return set(x for x in range(n) if abs(sc[x] - m) < 1e-9 and m > 0)


RULES = {"minmember": rule_minmember, "invsize": rule_invsize}


def all_union_closed(n):
    subs = list(range(1 << n))
    for bits in range(1, 1 << (1 << n)):
        fam = [s for s in subs if bits >> s & 1]
        if not any(s != 0 for s in fam):
            continue
        if all((a | b) in set(fam) for a in fam for b in fam):
            yield fam


def report_exhaustive(n):
    fails = {r: 0 for r in RULES}
    count = 0
    for fam in all_union_closed(n):
        count += 1
        ab = abundant(fam, n)
        for r, f in RULES.items():
            if not (f(fam, n) & ab):
                fails[r] += 1
    print(f"[n={n}] {count} union-closed families | " +
          " ".join(f"{r} fails={fails[r]}" for r in RULES))


def report_sampled(n, trials, seed, gensize=None, rare=None):
    random.seed(seed)
    pool = ([s for s in range(1 << n) if popcount(s) == gensize] if gensize
            else [s for s in range(1, 1 << n)])
    fails = {r: 0 for r in RULES}
    t = 0
    label = f"gensize={gensize}" if gensize else "random"
    for _ in range(trials):
        k = random.randint(2, min(8, len(pool)))
        gens = random.sample(pool, k)
        fam = close_union(gens)
        if len(fam) < 2 or not any(s for s in fam):
            continue
        t += 1
        ab = abundant(fam, n)
        for r, f in RULES.items():
            if not (f(fam, n) & ab):
                fails[r] += 1
    print(f"[n={n}, {label}] sampled {t} | " +
          " ".join(f"{r} fails={fails[r]}" for r in RULES))


if __name__ == "__main__":
    report_exhaustive(3)
    report_exhaustive(4)
    report_sampled(5, 20000, 2718)
    report_sampled(6, 20000, 6, gensize=3)
    report_sampled(7, 15000, 7, gensize=3)
    report_sampled(8, 8000, 8, gensize=4)
