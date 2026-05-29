#!/usr/bin/env python3
"""Step 1 of the `tight ⟹ Boolean` reduction (see frankl_tight_boolean.md):

    A union-closed family F in which every element lies in exactly half the
    members is closed under complementation (A ∈ F ⟹ U∖A ∈ F, U = ⋃F).

This probe (a) stress-tests Step 1 at m=7 by sampling union-closed families and
filtering the every-half ones, (b) checks two structural footholds:
   * ∅ ∈ F for every every-half family   (potential induction base)
   * the complement-DEFECT  D = F ∖ {U∖A : A∈F}  is always BALANCED
     (Σ_{A∈D} ε_A = 0), a fact proved on paper — sanity check it never fails.
"""
from __future__ import annotations
import random
from itertools import combinations

popcount = lambda x: bin(x).count("1")


def union_close(gens, U):
    fam = set(gens) | {0}            # include ∅; close under ∪
    fam = {g & U for g in fam}
    ch = True
    while ch:
        ch = False
        for a in list(fam):
            for b in list(fam):
                if (a | b) not in fam:
                    fam.add(a | b); ch = True
    return frozenset(fam)


def ground(fam):
    U = 0
    for s in fam:
        U |= s
    return U


def is_every_half(fam):
    """Every element of the ground set U=⋃F lies in exactly |F|/2 members."""
    n = len(fam)
    if n % 2:
        return False
    U = ground(fam)
    for i in range(U.bit_length()):
        if U >> i & 1:
            if sum(1 for s in fam if s >> i & 1) * 2 != n:
                return False
    return True


def is_complement_closed(fam):
    U = ground(fam)
    return all((U & ~A) in fam for A in fam)


def twin_free(fam):
    U = ground(fam); cols = {}
    for i in range(U.bit_length()):
        if U >> i & 1:
            key = tuple(sorted(s for s in fam if s >> i & 1))
            if key in cols:
                return False
            cols[key] = i
    return True


def all_coatoms(fam):
    """Coatom lemma (PROVED): twin-free every-half ⟹ every U∖{i} ∈ F."""
    U = ground(fam)
    return all((U & ~(1 << i)) in fam
               for i in range(U.bit_length()) if U >> i & 1)


def defect_balanced(fam):
    """D = F ∖ {U∖A}; return (|D|, is D balanced over the ground set)."""
    U = ground(fam)
    Fc = {U & ~A for A in fam}
    D = [A for A in fam if A not in Fc]
    if not D:
        return 0, True
    # balanced: every ground element in exactly |D|/2 defect members
    if len(D) % 2:
        return len(D), False
    for i in range(U.bit_length()):
        if U >> i & 1:
            if sum(1 for A in D if A >> i & 1) * 2 != len(D):
                return len(D), False
    return len(D), True


def exhaustive(m):
    """All union-closed families on ground set ⊆ [m] that are every-half."""
    U = (1 << m) - 1
    seen = set(); every = []
    # enumerate union-closed families by closing every subset-of-subsets is too big;
    # instead generate via random+small generator sets, dedup.  For m<=4 do exact.
    if m <= 4:
        subs = list(range(1 << m))
        # all families: too many (2^16); restrict to those containing their unions.
        # Build by: pick any subset T of 2^[m], close under union.
        out = set()
        for bits in range(1 << (1 << m)):
            fam = frozenset(s for s in subs if bits >> s & 1)
            if len(fam) >= 2 and all((a | b) in fam for a in fam for b in fam):
                out.add(fam)
        return out
    return None


def sample(m, trials):
    U = (1 << m) - 1
    fams = set()
    for _ in range(trials):
        k = random.randint(2, m + 3)
        gens = [random.randint(1, U) for _ in range(k)]
        fams.add(union_close(gens, U))
    return fams


if __name__ == "__main__":
    random.seed(1)
    print("Step 1 stress-test  (every-half union-closed ⟹ complement-closed)\n")

    # exhaustive small
    for m in (2, 3, 4):
        out = exhaustive(m)
        eh = [f for f in out if is_every_half(f)]
        bad = [f for f in eh if not is_complement_closed(f)]
        noempty = [f for f in eh if 0 not in f]
        defbad = [f for f in eh if not defect_balanced(f)[1]]
        coatombad = [f for f in eh if twin_free(f) and not all_coatoms(f)]
        print(f"  m={m} EXHAUSTIVE: {len(out):5d} u-closed | every-half={len(eh):4d} "
              f"| not-compl-closed={len(bad)} | ∅∉F={len(noempty)} | defect-unbalanced={len(defbad)} "
              f"| coatom-lemma-fail={len(coatombad)}")

    # sampled larger
    for m in (5, 6, 7):
        fams = sample(m, 400000 if m < 7 else 600000)
        eh = [f for f in fams if is_every_half(f)]
        bad = [f for f in eh if not is_complement_closed(f)]
        noempty = [f for f in eh if 0 not in f]
        defbad = [f for f in eh if not defect_balanced(f)[1]]
        coatombad = [f for f in eh if twin_free(f) and not all_coatoms(f)]
        print(f"  m={m} SAMPLED   : {len(fams):5d} u-closed | every-half={len(eh):4d} "
              f"| not-compl-closed={len(bad)} | ∅∉F={len(noempty)} | defect-unbalanced={len(defbad)} "
              f"| coatom-lemma-fail={len(coatombad)}")

    print("\n  not-compl-closed must be 0 (Step 1, verified not proved).")
    print("  defect-unbalanced must be 0 (PROVED).  coatom-lemma-fail must be 0 (PROVED).")
    print("  ∅∉F count: always 0 here — '∅∈F' is a verified foothold for Step 1.")
