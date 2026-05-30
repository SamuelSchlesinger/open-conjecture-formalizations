#!/usr/bin/env python3
"""Supplement to explore.py: (a) random-poset stress test for n = 6..9, and
(b) structural characterization of the exactly-1/3 extremal posets for n <= 5.

Random posets are drawn by picking a random linear order then keeping each
forward pair independently with prob p, then taking the transitive closure
(this samples a spread of posets including sparse and dense ones)."""
import random
from itertools import combinations
from fractions import Fraction
from explore import (transitive_closure, count_ext, count_before,
                     incomparable_pairs, is_leq, delta_of_poset, all_posets)

random.seed(12345)

def random_poset(n, p):
    perm = list(range(n)); random.shuffle(perm)
    less = set()
    for i in range(n):
        for j in range(i + 1, n):
            if random.random() < p:
                less.add((perm[i], perm[j]))
    return transitive_closure(n, less)

def stress(nmax=9, trials_per=4000):
    print("=" * 70)
    print("RANDOM STRESS TEST: delta(P) >= 1/3 on sampled posets, n = 6..%d" % nmax)
    print("=" * 70)
    for n in range(6, nmax + 1):
        worst = None; worst_less = None; tested = 0; violations = 0
        for _ in range(trials_per):
            p = random.choice([0.15, 0.25, 0.35, 0.5, 0.65])
            less = random_poset(n, p)
            if less is None:
                continue
            incs = incomparable_pairs(n, less)
            if not incs:
                continue
            tested += 1
            _, best, _, _, _ = delta_of_poset(n, less)
            if best < Fraction(1, 3):
                violations += 1
                print("  !!! VIOLATION n=%d less=%s delta=%s" % (n, sorted(less), best))
            if worst is None or best < worst:
                worst = best; worst_less = less
        print("n=%d: %d sampled non-chains, min delta found = %s (~%.4f), violations=%d"
              % (n, tested, worst, float(worst) if worst else 0, violations))
        if worst_less is not None:
            print("      worst-case poset (strict <): %s" % sorted(worst_less))

def characterize_extremal(nmax=5):
    print("=" * 70)
    print("STRUCTURE of exactly-1/3 extremal posets (n <= %d)" % nmax)
    print("=" * 70)
    for n in range(3, nmax + 1):
        found = []
        for less in all_posets(n):
            incs = incomparable_pairs(n, less)
            if not incs:
                continue
            eP, best, bp, info, _ = delta_of_poset(n, less)
            if best == Fraction(1, 3):
                # record e(P) and the minimal element / structure
                found.append((eP, less, bp, info))
        # group by e(P)
        from collections import Counter
        byE = Counter(eP for (eP, _, _, _) in found)
        print("n=%d: %d extremal (delta=1/3) labelled posets; e(P) multiset over them = %s"
              % (n, len(found), dict(sorted(byE.items()))))
        # show one representative per e(P) value
        seenE = set()
        for (eP, less, bp, info) in found:
            if eP in seenE:
                continue
            seenE.add(eP)
            x, y = bp
            bxy, byx = info[bp]
            print("    rep e=%d: <=%s  best pair {%d,%d}: before=%d/%d (=1/3 exactly: %s)"
                  % (eP, sorted(less), x, y, min(bxy, byx), eP, Fraction(min(bxy, byx), eP)))

if __name__ == "__main__":
    characterize_extremal(5)
    stress(9, trials_per=3000)
    print("\nDONE.")
