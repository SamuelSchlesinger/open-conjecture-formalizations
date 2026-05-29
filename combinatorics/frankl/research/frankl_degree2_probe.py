#!/usr/bin/env python3
"""Degree-2 / global attacks on Frankl, aimed at the gap our negatives identified
(first-order/marginal methods are barriered; the content is in 2nd-order
correlation structure).  Three experiments:

  (B) Second-moment inequality.  max_x mc_x >= (Σ mc_x^2)/(Σ mc_x) ALWAYS (weighted
      mean <= max).  So Frankl would follow from the degree-2 inequality
          I1:  Σ_x mc_x^2  >=  (|F|/2) Σ_x mc_x          [⟺ Σ|A∩B| >= (|F|/2)Σ|A|]
      Test I1; if false, measure the ratio R = (Σmc^2/Σmc)/(|F|/2) on the HARD
      families (p_max near 1/2) to see whether the 2nd-moment bound is tight
      enough to matter, or is itself barriered like averaging.

  (C) Compression.  Does the classic down-shift S_{i<-j} (send j->i where free)
      preserve union-closure?  If yes, it's a reduction tool.  Test preservation
      + whether it keeps |F| and never worsens the Frankl deficiency.

  (E) Spectral.  Relate p_max to the top eigenvalue of the m x m correlation
      matrix M^T M (M = |F| x m incidence).  Is p_max >= λ_max/|F| useful?
"""
from __future__ import annotations
import random
from itertools import combinations

popcount = lambda x: bin(x).count("1")


def union_close(gens, U):
    fam = {0} | {g & U for g in gens}
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


def is_union_closed(fam):
    return all((a | b) in fam for a in fam for b in fam)


def stats(fam):
    U = ground(fam); n = len(fam)
    pts = [i for i in range(U.bit_length()) if U >> i & 1]
    mc = {i: sum(1 for s in fam if s >> i & 1) for i in pts}
    if not mc:
        return None
    S1 = sum(mc.values())                       # Σ mc = Σ|A|
    S2 = sum(v * v for v in mc.values())        # Σ mc^2 = Σ|A∩B|
    mx = max(mc.values())
    return dict(n=n, m=len(pts), mc=mc, S1=S1, S2=S2, mx=mx)


# ---- (B) second-moment inequality ----------------------------------------
def test_I1(fam):
    st = stats(fam)
    if st is None or st["S1"] == 0:
        return None
    n = st["n"]
    I1 = (2 * st["S2"] >= n * st["S1"])             # Σmc^2 >= (n/2)Σmc
    p_max = st["mx"] / n
    second_bound = (st["S2"] / st["S1"]) / (n / 2)  # R: how close 2nd-moment bound is to 1/2
    frankl = (2 * st["mx"] >= n)
    return dict(I1=I1, p_max=p_max, R=second_bound, frankl=frankl, n=n)


# ---- (C) compression ------------------------------------------------------
def down_shift(fam, i, j):
    """Send element j -> i: for A with j∈A, i∉A, try replacing j by i unless the
    image already in fam (classic compression keeping |F|)."""
    out = set()
    for A in fam:
        if (A >> j & 1) and not (A >> i & 1):
            B = (A & ~(1 << j)) | (1 << i)
            out.add(B if B not in fam else A)
        else:
            out.add(A)
    return frozenset(out)


def test_compression(fam):
    U = ground(fam)
    pts = [i for i in range(U.bit_length()) if U >> i & 1]
    broke_uc = same_card = improved = 0
    trials = 0
    for i in pts:
        for j in pts:
            if i == j:
                continue
            trials += 1
            g = down_shift(fam, i, j)
            if len(g) != len(fam):
                same_card += 1                      # count card CHANGES
            if not is_union_closed(g):
                broke_uc += 1
    return dict(trials=trials, broke_uc=broke_uc, card_changed=same_card)


# ---- (E) spectral ---------------------------------------------------------
def test_spectral(fam):
    try:
        import numpy as np
    except ImportError:
        return None
    U = ground(fam)
    pts = [i for i in range(U.bit_length()) if U >> i & 1]
    if not pts:
        return None
    M = np.array([[1.0 if s >> i & 1 else 0.0 for i in pts] for s in fam])
    MtM = M.T @ M
    lam = max(np.linalg.eigvalsh(MtM))
    n = len(fam)
    p_max = max(MtM[k, k] for k in range(len(pts))) / n
    return dict(p_max=p_max, lam_over_n=lam / n, useful=(lam / n >= n / 2))


def families(m, exact_upto=4, samples=200000):
    U = (1 << m) - 1
    if m <= exact_upto:
        subs = list(range(1 << m)); out = set()
        for bits in range(1 << (1 << m)):
            fam = frozenset(s for s in subs if bits >> s & 1)
            if len(fam) >= 2 and is_union_closed(fam):
                out.add(fam)
        return out
    fams = set()
    for _ in range(samples):
        k = random.randint(2, m + 3)
        fams.add(union_close([random.randint(1, U) for _ in range(k)], U))
    return {f for f in fams if len(f) >= 2}


if __name__ == "__main__":
    random.seed(0)
    print("=== (B) second-moment inequality I1: Σmc^2 >= (|F|/2)Σmc  ⟹ Frankl ===")
    worst_R = (9.9, None)
    for m in (2, 3, 4, 5, 6):
        fl = families(m)
        I1_fail = hard = 0; minR = 9.9; minR_at_hard = 9.9
        for fam in fl:
            r = test_I1(fam)
            if r is None:
                continue
            if not r["I1"]:
                I1_fail += 1
            minR = min(minR, r["R"])
            if r["p_max"] <= 0.5 + 1e-9:           # HARD: extremal/at the bound
                hard += 1
                minR_at_hard = min(minR_at_hard, r["R"])
        print(f"  m={m}: {len(fl):5d} families | I1 fails={I1_fail:5d} "
              f"| min R(all)={minR:.3f} | hard(p_max≤½)={hard} min R(hard)={minR_at_hard:.3f}")
    print("  I1 fails > 0 ⟹ the plain 2nd-moment inequality does NOT prove Frankl.")
    print("  R<1 on hard families ⟹ 2nd-moment bound also undershoots ½ there.\n")

    print("=== (C) compression: does down-shift preserve union-closure? ===")
    for m in (3, 4, 5):
        fl = families(m)
        tot_trials = tot_broke = tot_changed = 0
        for fam in fl:
            c = test_compression(fam)
            tot_trials += c["trials"]; tot_broke += c["broke_uc"]
            tot_changed += c["card_changed"]
        print(f"  m={m}: {len(fl):5d} families, {tot_trials} shifts | "
              f"broke union-closure={tot_broke} | changed |F|={tot_changed}")
    print("  broke>0 ⟹ naive down-shift is NOT union-closure-preserving (expected).\n")

    print("=== (E) spectral: is λ_max(M^T M)/|F| >= |F|/2 (⟹ Frankl)? ===")
    for m in (3, 4, 5):
        fl = families(m)
        useful = 0; tot = 0
        for fam in fl:
            s = test_spectral(fam)
            if s is None:
                continue
            tot += 1
            if s["useful"]:
                useful += 1
        print(f"  m={m}: {tot} families | λ-bound certifies Frankl in {useful}/{tot}")
