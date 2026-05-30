#!/usr/bin/env python3
"""
Computational exploration of the 1/3-2/3 conjecture (Phase 3).

For a finite poset P:
  e(P)         = number of linear extensions
  e(P, x<y)    = number of linear extensions with x before y
  delta(x,y)   = e(P,x<y)/e(P)
  delta(P)     = max over incomparable {x,y} of min(delta(x,y), delta(y,x))

The conjecture: every non-chain poset has delta(P) >= 1/3.

We:
  1. Enumerate all labelled posets on n<=5 elements (every iso class represented),
     verify delta(P) >= 1/3, and find the extremal posets (min delta).
  2. Compute e and the before-counts exactly via the 2^n order-ideal DP.
  3. Test candidate REDUCTIONS (the "Frankl playbook"):
       - duality (P vs P^op): should preserve delta exactly;
       - element deletion: does a balanced pair of P minus z lift to P?
       - disjoint union and ordinal (linear) sum.
  4. Test SELECTION RULES: can a *local* rule always pick a balanced pair?
  5. Compute named families for larger n (V_n, ordinal sums, "Sah" width-2 chains).

All counts are exact integers (Fraction for ratios).
"""
from itertools import combinations, product
from fractions import Fraction
from functools import lru_cache

# ----------------------------------------------------------------------------
# Poset representation: relation matrix `leq[i][j] = (i <= j)`, n elements.
# We store the strict relation as a frozenset of (i,j) with i<j meaning i below j.
# ----------------------------------------------------------------------------

def transitive_closure(n, less):
    """less: set of (i,j) meaning i<j. Return transitively closed set, or None if a cycle/antisym fails."""
    L = set(less)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(L):
            for (c, d) in list(L):
                if b == c and (a, d) not in L:
                    L.add((a, d)); changed = True
    # irreflexive + antisymmetric check
    for (a, b) in L:
        if a == b:
            return None
        if (b, a) in L:
            return None
    return frozenset(L)

def all_posets(n):
    """Yield every labelled poset on [n] as a transitively-closed strict relation (frozenset)."""
    pairs = list(combinations(range(n), 2))   # unordered pairs
    seen = set()
    # each pair: i<j, j<i, or incomparable
    for choice in product((0, 1, 2), repeat=len(pairs)):
        less = set()
        for (i, j), c in zip(pairs, choice):
            if c == 1:
                less.add((i, j))
            elif c == 2:
                less.add((j, i))
        tc = transitive_closure(n, less)
        if tc is None:
            continue
        # only keep if the transitive closure introduces no NEW comparabilities
        # among our chosen pairs beyond what we set (otherwise double-count); we
        # accept tc and dedup by the closed relation.
        if tc not in seen:
            seen.add(tc)
            yield tc

def is_leq(less, i, j):
    return i == j or (i, j) in less

def incomparable_pairs(n, less):
    res = []
    for i, j in combinations(range(n), 2):
        if not is_leq(less, i, j) and not is_leq(less, j, i):
            res.append((i, j))
    return res

# ----------------------------------------------------------------------------
# Counting linear extensions via order-ideal DP.
# f(S) = number of linear orders of the induced poset on S consistent with <.
# f(S) = sum over maximal elements m of S of f(S \ {m}).
# e(P) = f(full).  before(x<y): we count extensions where x precedes y by a
#         second DP that forbids placing y before x.  Simpler: enumerate via the
#         "build from the top" DP but track relative order — instead we use the
#         linearity: e(P, x<y) = (extensions with x before y). We compute it as
#         e of the poset P + (x<y) relation (adding x<y), which counts exactly the
#         extensions placing x before y.  (Adding the relation x<y keeps it a poset
#         since x,y incomparable.)
# ----------------------------------------------------------------------------

def count_ext(n, less):
    full = (1 << n) - 1
    # precompute, for each element, its set of (strict) lower covers bitmask
    below = [0] * n   # bitmask of elements strictly below i
    for (a, b) in less:
        below[b] |= (1 << a)

    from functools import lru_cache
    @lru_cache(maxsize=None)
    def f(S):
        if S == 0:
            return 1
        total = 0
        # m is maximal in S if no element of S is strictly above m, i.e.
        # no k in S with m below k  => for all k in S, m not in below[k].
        for m in range(n):
            if not (S & (1 << m)):
                continue
            # m maximal in S: no k in S with (m,k) in less
            is_max = True
            rest = S & ~(1 << m)
            kk = rest
            while kk:
                k = (kk & -kk).bit_length() - 1
                kk &= kk - 1
                if (m, k) in less:
                    is_max = False
                    break
            if is_max:
                total += f(rest)
        return total
    res = f(full)
    f.cache_clear()
    return res

def count_before(n, less, x, y):
    """Number of linear extensions with x before y (x,y incomparable)."""
    less2 = transitive_closure(n, set(less) | {(x, y)})
    return count_ext(n, less2)

def delta_of_poset(n, less):
    """Return (eP, best_min_ratio as Fraction, best_pair, dict pair->(bxy,byx))."""
    eP = count_ext(n, less)
    incs = incomparable_pairs(n, less)
    info = {}
    best = None
    best_pair = None
    for (x, y) in incs:
        bxy = count_before(n, less, x, y)
        byx = eP - bxy
        info[(x, y)] = (bxy, byx)
        m = min(bxy, byx)
        r = Fraction(m, eP)
        if best is None or r > best:
            best = r; best_pair = (x, y)
    return eP, best, best_pair, info, incs

# ----------------------------------------------------------------------------
# 1+2: enumerate, verify, find extremal
# ----------------------------------------------------------------------------

def study(nmax=5):
    print("=" * 70)
    print("ENUMERATION: delta(P) over all labelled posets, n = 1..%d" % nmax)
    print("=" * 70)
    overall_min = None
    overall_min_examples = []
    for n in range(1, nmax + 1):
        cnt = 0
        nonchain = 0
        minr = None
        min_examples = []
        violations = 0
        for less in all_posets(n):
            cnt += 1
            incs = incomparable_pairs(n, less)
            if not incs:
                continue  # chain
            nonchain += 1
            eP, best, bp, info, _ = delta_of_poset(n, less)
            if best < Fraction(1, 3):
                violations += 1
                print("  !!! VIOLATION n=%d less=%s delta=%s" % (n, sorted(less), best))
            if minr is None or best < minr:
                minr = best
                min_examples = [less]
            elif best == minr:
                if len(min_examples) < 6:
                    min_examples.append(less)
        print("n=%d: %d labelled posets, %d non-chains, min delta(P)=%s, violations=%d"
              % (n, cnt, nonchain, minr, violations))
        if minr is not None:
            for ex in min_examples[:3]:
                print("      extremal poset (strict <): %s  delta=%s" % (sorted(ex), minr))
            if overall_min is None or minr < overall_min:
                overall_min = minr
    print("Overall min delta over n<=%d: %s  (= %.5f)" % (nmax, overall_min, float(overall_min)))
    return overall_min

# ----------------------------------------------------------------------------
# 3: reductions
# ----------------------------------------------------------------------------

def dual(n, less):
    return frozenset((b, a) for (a, b) in less)

def test_duality(nmax=5):
    print("=" * 70)
    print("REDUCTION TEST: duality delta(P) == delta(P^op)?")
    print("=" * 70)
    bad = 0; tested = 0
    for n in range(2, nmax + 1):
        for less in all_posets(n):
            if not incomparable_pairs(n, less):
                continue
            tested += 1
            _, d1, _, _, _ = delta_of_poset(n, less)
            ld = dual(n, less)
            _, d2, _, _, _ = delta_of_poset(n, ld)
            if d1 != d2:
                bad += 1
                if bad <= 3:
                    print("  mismatch: %s d=%s vs dual d=%s" % (sorted(less), d1, d2))
    print("duality: tested %d non-chain posets (n<=%d), delta != delta^op in %d cases"
          % (tested, nmax, bad))

def test_deletion(nmax=5):
    """Does 'P has balanced pair iff some single-element deletion does' hold?
    More precisely: test whether a balanced pair of P\\{z} (restricted) is still a
    balanced pair in P (lift), and whether every P's balanced pair survives a deletion."""
    print("=" * 70)
    print("REDUCTION TEST: does a balanced pair lift across element deletion?")
    print("=" * 70)
    lift_fail = 0; tested = 0; examples = []
    for n in range(3, nmax + 1):
        for less in all_posets(n):
            if not incomparable_pairs(n, less):
                continue
            tested += 1
            eP, bestP, bpP, _, _ = delta_of_poset(n, less)
            # For each z, look at P\{z}: relabel remaining to 0..n-2
            for z in range(n):
                rem = [v for v in range(n) if v != z]
                idx = {v: i for i, v in enumerate(rem)}
                less_sub = frozenset((idx[a], idx[b]) for (a, b) in less if a != z and b != z)
                m = n - 1
                if not incomparable_pairs(m, less_sub):
                    continue
                _, bestSub, bpSub, _, _ = delta_of_poset(m, less_sub)
                # lift bpSub back to P: which original pair is it?
                inv = {i: v for v, i in idx.items()}
                (sx, sy) = bpSub
                (ox, oy) = inv[sx], inv[sy]
                # is (ox,oy) a balanced pair in P?
                if not is_leq(less, ox, oy) and not is_leq(less, oy, ox):
                    bxy = count_before(n, less, ox, oy)
                    byx = eP - bxy
                    bal = (eP <= 3 * bxy) and (3 * bxy <= 2 * eP)
                    if not bal:
                        lift_fail += 1
                        if len(examples) < 4:
                            examples.append((n, sorted(less), z, (ox, oy)))
                # else the sub-balanced-pair became comparable in P (can't lift)
    print("deletion-lift: tested %d non-chain posets; sub-balanced-pair NOT balanced in P "
          "in %d (z,pair) instances" % (tested, lift_fail))
    for ex in examples:
        print("   counterexample: n=%d less=%s delete z=%d sub-pair lifts to %s (not balanced)"
              % ex)

# ----------------------------------------------------------------------------
# 4: selection rules — can a local rule always find a balanced pair?
# ----------------------------------------------------------------------------

def test_selection_rules(nmax=5):
    print("=" * 70)
    print("SELECTION RULES: does a simple local rule always pick a BALANCED pair?")
    print("=" * 70)
    rules = {}
    def balanced(eP, bxy):
        return (eP <= 3 * bxy) and (3 * bxy <= 2 * eP)

    # rule A: pick the incomparable pair with smallest |2*bxy - eP| (closest to 1/2) -- "oracle-ish"
    # rule B: pick first incomparable pair (lexicographic) -- naive
    # rule C: pick incomparable pair (x,y) where x,y are both minimal elements
    # rule D: pick incomparable pair maximizing degree (most comparabilities) ...
    failA = failB = failC = 0
    nA = nB = nC = 0
    for n in range(2, nmax + 1):
        for less in all_posets(n):
            incs = incomparable_pairs(n, less)
            if not incs:
                continue
            eP = count_ext(n, less)
            bcount = {}
            for (x, y) in incs:
                bcount[(x, y)] = count_before(n, less, x, y)
            # rule B: first incomparable pair
            (x, y) = incs[0]
            nB += 1
            if not balanced(eP, bcount[(x, y)]):
                failB += 1
            # rule C: both minimal
            minimal = [v for v in range(n) if all((u, v) not in less for u in range(n))]
            cpair = None
            for (x, y) in incs:
                if x in minimal and y in minimal:
                    cpair = (x, y); break
            if cpair is not None:
                nC += 1
                if not balanced(eP, bcount[cpair]):
                    failC += 1
            # rule A: pick pair minimizing |2b - e|
            best = min(incs, key=lambda p: abs(2 * bcount[p] - eP))
            nA += 1
            if not balanced(eP, bcount[best]):
                failA += 1
    print("rule A (min |2b-e|, closest to 1/2): %d/%d FAILED to be balanced" % (failA, nA))
    print("rule B (first incomparable pair):     %d/%d FAILED" % (failB, nB))
    print("rule C (both elements minimal):       %d/%d FAILED (when applicable)" % (failC, nC))
    print("Interpretation: rule A failing >0 would mean even the *most balanced* pair")
    print("can fall outside [1/3,2/3] -- it must NOT fail if the conjecture holds (n<=%d)." % nmax)

# ----------------------------------------------------------------------------
# 5: named families for larger n
# ----------------------------------------------------------------------------

def family_Vn(k):
    """A chain a_1<...<a_k plus one extra element c incomparable to all: 'broom'."""
    n = k + 1
    less = set()
    for i in range(k - 1):
        less.add((i, i + 1))
    less = transitive_closure(n, less)
    return n, less

def family_ordinal_sum_of_antichains(sizes):
    """Ordinal sum A_{s1} ⊕ A_{s2} ⊕ ... : each block an antichain, blocks stacked."""
    n = sum(sizes)
    less = set()
    offsets = []
    o = 0
    for s in sizes:
        offsets.append(o); o += s
    for bi in range(len(sizes)):
        for bj in range(bi + 1, len(sizes)):
            for a in range(offsets[bi], offsets[bi] + sizes[bi]):
                for b in range(offsets[bj], offsets[bj] + sizes[bj]):
                    less.add((a, b))
    return n, transitive_closure(n, less)

def study_families():
    print("=" * 70)
    print("NAMED FAMILIES (larger n)")
    print("=" * 70)
    for k in range(2, 7):
        n, less = family_Vn(k)
        eP, best, bp, info, incs = delta_of_poset(n, less)
        print("broom: chain of %d + 1 free elt (n=%d): e=%d, delta(P)=%s (~%.4f)"
              % (k, n, eP, best, float(best)))
    for sizes in [(1, 2), (2, 1), (1, 1, 1), (2, 2), (1, 2, 1), (2, 1, 2), (3, 3)]:
        n, less = family_ordinal_sum_of_antichains(sizes)
        if not incomparable_pairs(n, less):
            print("ordinal sum antichains %s (n=%d): CHAIN" % (sizes, n)); continue
        eP, best, bp, info, incs = delta_of_poset(n, less)
        print("ordinal sum of antichains %s (n=%d): e=%d, delta(P)=%s (~%.4f)"
              % (sizes, n, eP, best, float(best)))

if __name__ == "__main__":
    study(5)
    study_families()
    test_duality(5)
    test_deletion(5)
    test_selection_rules(5)
    print("\nDONE.")
