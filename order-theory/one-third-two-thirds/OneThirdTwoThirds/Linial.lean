import OneThirdTwoThirds.TwoChains

/-!
# The 1/3–2/3 conjecture — Linial's width-2 mechanism

Linial (1984) proved the conjecture for posets of width ≤ 2.  Modelling a
width-2 poset as two chains `A`, `B` (Dilworth), the linear extensions are
monotone lattice paths in a staircase region, and Linial's argument is a
**discrete intermediate-value sweep** along the antidiagonal of incomparable
pairs: one walks a sequence of incomparable pairs from a low-`δ` corner to a
high-`δ` corner, in which each unit step changes the before-count by at most a
third of `e(P)`, so the sweep must cross the balanced band `[1/3, 2/3]`.

This file isolates the **engine** of that argument — independent of the
lattice-path counting — as `balancedPair_of_sweep`: *any* monotone sweep of
incomparable pairs whose before-counts satisfy the three intermediate-value
hypotheses produces a balanced pair.  It is the poset-level wrapper of
`balanced_of_monotone_steps` (proved in `TwoChains`).

With this engine, **the entire content of Linial's width-2 theorem reduces to
constructing such a sweep** for a 2-chain poset and bounding its steps by `1/3`
(the lattice-path counting) — exactly as the two-chains kernel
(`TwoChainsCount`) did for the *rectangular* region of a disjoint union, where
the sweep is the `a₀`-row.  That construction for a general staircase region is
the remaining (counting) milestone; `sorry`-free here.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {X : Type*} [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]

/-- **The Linial sweep engine.**  Let `x k, y k` be a length-`(N+1)` sequence of
incomparable pairs of a poset `P`.  If the before-counts `e(P, x k < y k)`
* start at most two-thirds: `3·e(P, x 0 < y 0) ≤ 2·e(P)`,
* increase per step by at most a third: `3·e(P, x_{k+1}<y_{k+1}) ≤ 3·e(P, x_k<y_k) + e(P)`,
* end at least a third: `e(P) ≤ 3·e(P, x_N < y_N)`,

then some pair `{x k, y k}` along the sweep is **balanced**, so `P` satisfies the
1/3–2/3 conjecture.  (This is Linial's intermediate-value argument; the engine is
`balanced_of_monotone_steps`, applied to `d k = e(P, x k < y k)` with `D = e(P)`.) -/
theorem balancedPair_of_sweep {N : ℕ} (x y : ℕ → X)
    (hincomp : ∀ k, k ≤ N → Incomp (x k) (y k))
    (hstep : ∀ k, k < N →
      3 * numBefore (x (k + 1)) (y (k + 1)) ≤ 3 * numBefore (x k) (y k) + numLinExts (X := X))
    (hstart : 3 * numBefore (x 0) (y 0) ≤ 2 * numLinExts (X := X))
    (hend : numLinExts (X := X) ≤ 3 * numBefore (x N) (y N)) :
    ∃ a b : X, IsBalancedPair a b := by
  obtain ⟨k, hkN, h1, h2⟩ :=
    balanced_of_monotone_steps (D := numLinExts (X := X)) (N := N)
      (fun k => numBefore (x k) (y k)) hstep hstart hend
  exact ⟨x k, y k, hincomp k hkN, h1, h2⟩

/-- The conjecture for a poset, obtained from a balanced pair produced by a
sweep — the form in which `balancedPair_of_sweep` feeds `OneThirdTwoThirdsFor`. -/
theorem oneThirdTwoThirdsFor_of_balancedPair
    (h : ∃ a b : X, IsBalancedPair a b) : OneThirdTwoThirdsFor (X := X) :=
  fun _ => h

end OneThirdTwoThirds
