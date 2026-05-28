#!/usr/bin/env python3
"""Fiber-injection FC-family certificates for Frankl's union-closed conjecture.

A family ``A`` of subsets of ``[n]`` is *FC* (Frankl-complete) if every finite
union-closed family ``F`` with ``A ⊆ F`` has an element of ``[n]`` lying in at
least half of the member-sets.  Poonen's theorem (see Bruhn--Schaudt survey;
arXiv:2301.01331, Thm 1.1) characterizes FC-families by ground-set weights
``c ≥ 0``, ``Σ cᵢ = 1`` with ``Σᵢ cᵢ |Bᵢ| ≥ |B|/2`` for every union-closed
``B ⊇ A`` on ``[n]``.

This module produces a *sound, self-contained* certificate that is directly
formalizable in Lean (it generalizes the singleton/doubleton proofs):

Group any union-closed ``F ⊇ A`` by trace ``T = B ∩ [n]`` with fiber counts
``m_T = #{B ∈ F : B ∩ [n] = T}``.  For ``W ∈ ⟨A⟩`` and ``T`` with ``T ∩ W = ∅``,
the map ``B ↦ B ∪ W`` injects fiber ``T`` into fiber ``T ∪ W``, so

    (INJ_{W,T})      m_T ≤ m_{T ∪ W}.

If there are weights ``c`` and Farkas multipliers ``λ_{W,T} ≥ 0`` (plus slacks
``s_T ≥ 0``) with, for every ``T ⊆ [n]``,

    w_c(T) − 1/2  =  Σ_{W ∈ ⟨A⟩, W ⊆ T} λ_{W, T∖W}
                     − Σ_{W ∈ ⟨A⟩, W ∩ T = ∅} λ_{W, T}
                     + s_T,                                    (DUAL)

where ``w_c(T) = Σ_{i ∈ T} cᵢ``, then summing over ``T`` against ``m_T`` gives

    Σ_T m_T (w_c(T) − 1/2) = Σ λ_{W,T} (m_{T∪W} − m_T) + Σ s_T m_T ≥ 0,

i.e. ``Σ_i cᵢ · count_i(F) ≥ |F|/2``, so some ``i`` with ``cᵢ > 0`` is abundant.
(DUAL) is the coefficient-matching identity for the polynomial in the ``m_T``.

The certificate ``(c, λ, s)`` is found by LP and re-verified exactly over ℚ.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from typing import Dict, List, Tuple

import numpy as np
from scipy.optimize import linprog


# ---------------------------------------------------------------------------
# Bitmask helpers for subsets of [n] = {0, ..., n-1}
# ---------------------------------------------------------------------------

def popcount(x: int) -> int:
    return bin(x).count("1")


def subsets(n: int) -> List[int]:
    return list(range(1 << n))


def closure_under_union(gens: List[int]) -> List[int]:
    """Union (bitwise-OR) closure of the generating masks."""
    closed = set(gens)
    frontier = list(closed)
    while frontier:
        x = frontier.pop()
        for y in list(closed):
            z = x | y
            if z not in closed:
                closed.add(z)
                frontier.append(z)
    return sorted(closed)


def mask_str(x: int, n: int) -> str:
    if x == 0:
        return "∅"
    return "{" + ",".join(str(i) for i in range(n) if x & (1 << i)) + "}"


# ---------------------------------------------------------------------------
# Ground truth: Poonen FC-check by full enumeration (small n only)
# ---------------------------------------------------------------------------

def all_union_closed_families(n: int) -> List[Tuple[int, ...]]:
    """Every union-closed B ⊆ 2^[n], as sorted tuples of masks.  Feasible n≤4."""
    universe = subsets(n)
    out = []
    # iterate over all subsets of 2^[n]
    for bits in range(1 << (1 << n)):
        fam = [m for m in universe if bits & (1 << m)]
        ok = True
        fs = set(fam)
        for a in fam:
            for b in fam:
                if (a | b) not in fs:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.append(tuple(fam))
    return out


def is_fc_by_poonen(A: List[int], n: int) -> Tuple[bool, Dict]:
    """Decide FC via Poonen's weight LP over ALL union-closed B ⊇ A on [n]."""
    Aset = set(closure_under_union(A))
    fams = [f for f in all_union_closed_families(n) if Aset.issubset(set(f))]
    # Variables c_0..c_{n-1} >= 0, sum = 1.
    # For each family B: sum_i c_i |B_i| >= |B|/2  ->  -(sum_i c_i |B_i|) <= -|B|/2
    A_ub = []
    b_ub = []
    for f in fams:
        coeff = [0.0] * n
        for m in f:
            for i in range(n):
                if m & (1 << i):
                    coeff[i] += 1.0
        A_ub.append([-x for x in coeff])
        b_ub.append(-len(f) / 2.0)
    A_eq = [[1.0] * n]
    b_eq = [1.0]
    res = linprog(c=[0.0] * n, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0.0, None)] * n, method="highs")
    return bool(res.success), {"num_families": len(fams), "weights": None if not res.success else list(res.x)}


# ---------------------------------------------------------------------------
# Fiber-injection Farkas certificate (the formalizable object)
# ---------------------------------------------------------------------------

def injection_pairs(Wmasks: List[int], n: int) -> List[Tuple[int, int]]:
    """All nontrivial injections (W, T): W ∈ ⟨A⟩, W ≠ ∅, T ⊆ [n], W ⊄ T.

    Since W ⊆ [n], the map B ↦ B ∪ W is injective on the trace fiber T for ANY
    T (B ∩ W = T ∩ W is forced, so B ∖ W determines B), landing in fiber T ∪ W.
    Hence m_T ≤ m_{T∪W}; we keep only W ⊄ T (else T∪W = T, trivial)."""
    out = []
    full = (1 << n) - 1
    for W in Wmasks:
        if W == 0:
            continue
        for T in range(1 << n):
            if (W & ~T & full) != 0:  # W not subset of T
                out.append((W, T))
    return out


def find_certificate(A: List[int], n: int) -> Dict:
    """Find weights c and Farkas multipliers via LP, then verify exactly over ℚ.

    Returns dict with keys: feasible (bool), and on success c, lam, slack.
    """
    Wmasks = closure_under_union(A)
    pairs = injection_pairs(Wmasks, n)  # list of (W, T)
    Ts = subsets(n)
    # Variables: c_i (n), lam_{W,T} (len(pairs)), s_T (2^n).  All >= 0.
    nc = n
    nl = len(pairs)
    ns = 1 << n
    nvar = nc + nl + ns
    idx_c = lambda i: i
    idx_l = {pair: nc + k for k, pair in enumerate(pairs)}
    idx_s = lambda T: nc + nl + T

    # Equality constraints (DUAL), one per T:
    #   sum_{i in T} c_i
    #   - sum_{W subseteq T} lam_{W, T\W}
    #   + sum_{W ∩ T = ∅} lam_{W, T}
    #   - s_T
    #   = 1/2
    A_eq = []
    b_eq = []
    for T in Ts:
        row = [0.0] * nvar
        for i in range(n):
            if T & (1 << i):
                row[idx_c(i)] += 1.0
        for (W, Tp) in pairs:
            # target term −λ_{W,Tp}: this injection's upper set Tp∪W equals S=T
            if (Tp | W) == T:
                row[idx_l[(W, Tp)]] += -1.0
            # source term +λ_{W,Tp}: this injection's lower set Tp equals S=T
            if Tp == T:
                row[idx_l[(W, Tp)]] += 1.0
        row[idx_s(T)] += -1.0
        A_eq.append(row)
        b_eq.append(0.5)
    # also sum c_i = 1 to pin down scale (optional but keeps weights normalized)
    row = [0.0] * nvar
    for i in range(n):
        row[idx_c(i)] = 1.0
    A_eq.append(row)
    b_eq.append(1.0)

    res = linprog(c=[0.0] * nvar, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0.0, None)] * nvar, method="highs")
    if not res.success:
        return {"feasible": False}

    x = res.x
    c = [rationalize(x[idx_c(i)]) for i in range(n)]
    lam = {pair: rationalize(x[idx_l[pair]]) for pair in pairs if x[idx_l[pair]] > 1e-9}
    slack = {T: rationalize(x[idx_s(T)]) for T in Ts if x[idx_s(T)] > 1e-9}

    ok = verify_certificate(A, n, c, lam, slack)
    return {"feasible": True, "exact_verified": ok, "c": c, "lam": lam, "slack": slack,
            "Wmasks": Wmasks}


def rationalize(x: float, max_den: int = 360) -> Fraction:
    return Fraction(x).limit_denominator(max_den)


def verify_certificate(A: List[int], n: int, c: List[Fraction],
                       lam: Dict[Tuple[int, int], Fraction],
                       slack: Dict[int, Fraction]) -> bool:
    """Exactly verify (DUAL) holds for every T and all multipliers are >= 0."""
    if any(v < 0 for v in c):
        return False
    if any(v < 0 for v in lam.values()):
        return False
    if any(v < 0 for v in slack.values()):
        return False
    if sum(c) != 1:
        return False
    for T in subsets(n):
        lhs = sum((c[i] for i in range(n) if T & (1 << i)), Fraction(0)) - Fraction(1, 2)
        rhs = Fraction(0)
        for (W, Tp), val in lam.items():
            # +λ_{W,Tp} when Tp∪W = T (T is this injection's upper/target set)
            if (Tp | W) == T:
                rhs += val
            # −λ_{W,Tp} when Tp = T (T is this injection's lower/source set)
            if Tp == T:
                rhs -= val
        rhs += slack.get(T, Fraction(0))
        if lhs != rhs:
            return False
    return True


# ---------------------------------------------------------------------------
# Reporting / search
# ---------------------------------------------------------------------------

def describe(A: List[int], n: int) -> str:
    return "{" + ", ".join(mask_str(m, n) for m in A) + "}"


def report_family(A: List[int], n: int) -> Dict:
    fc, info = is_fc_by_poonen(A, n)
    cert = find_certificate(A, n)
    return {
        "family": describe(A, n),
        "masks": A,
        "n": n,
        "poonen_fc": fc,
        "poonen_num_families": info["num_families"],
        "fiber_certificate_feasible": cert["feasible"],
        "fiber_certificate_exact": cert.get("exact_verified", False),
        "certificate": _cert_to_json(cert, n) if cert["feasible"] else None,
    }


def _cert_to_json(cert: Dict, n: int) -> Dict:
    return {
        "weights": {f"c_{i}": str(cert["c"][i]) for i in range(n)},
        "injection_multipliers": {
            f"lam[W={mask_str(W, n)},T={mask_str(T, n)}]": str(v)
            for (W, T), v in cert["lam"].items()
        },
        "slacks": {f"s[T={mask_str(T, n)}]": str(v) for T, v in cert["slack"].items()},
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--validate", action="store_true",
                    help="Validate engine on singleton and doubleton.")
    ap.add_argument("--search-3sets", type=int, metavar="N",
                    help="Search families of 3-sets on ground set [N] for FC.")
    ap.add_argument("--emit", type=str, metavar="PATH",
                    help="Emit certificate JSON for the chosen family to PATH.")
    args = ap.parse_args()

    if args.validate:
        print("== Validation ==")
        for A, n, name in [([0b01], 1, "singleton {0}"),
                           ([0b1], 1, "singleton on n=1"),
                           ([0b11], 2, "doubleton {0,1}")]:
            r = report_family(A, n)
            print(f"\n{name}: {r['family']}  (n={n})")
            print(f"  Poonen FC: {r['poonen_fc']}  (checked {r['poonen_num_families']} families)")
            print(f"  fiber certificate feasible/exact: "
                  f"{r['fiber_certificate_feasible']}/{r['fiber_certificate_exact']}")
            if r["certificate"]:
                print(f"  weights: {r['certificate']['weights']}")
                print(f"  injections used: {r['certificate']['injection_multipliers']}")

    if args.search_3sets is not None:
        n = args.search_3sets
        print(f"\n== Searching families of 3-sets on [{n}] ==")
        threes = [m for m in subsets(n) if popcount(m) == 3]
        full = (1 << n) - 1
        found = []
        # single 3-sets, then pairs, then triples of 3-sets that cover [n]
        for size in (1, 2, 3, 4):
            for combo in itertools.combinations(threes, size):
                A = list(combo)
                # require U(A) = [n] so Poonen's ground set is exactly [n]
                cover = 0
                for m in A:
                    cover |= m
                if cover != full:
                    continue
                fc, info = is_fc_by_poonen(A, n)
                if fc:
                    cert = find_certificate(A, n)
                    found.append((A, cert))
                    status = "exact" if cert.get("exact_verified") else (
                        "feasible(float)" if cert["feasible"] else "NO fiber cert")
                    print(f"  FC: {describe(A, n)}  fiber-cert: {status}")
            if found:
                break  # report the smallest size that yields FC families
        if not found:
            print("  no FC family of 3-sets found at this size on this ground set")

    if args.emit:
        # default emitted family: the doubleton (smallest nontrivial FC certificate)
        A, n = [0b11], 2
        r = report_family(A, n)
        with open(args.emit, "w") as fh:
            json.dump(r, fh, indent=2)
        print(f"wrote {args.emit}")


if __name__ == "__main__":
    main()
