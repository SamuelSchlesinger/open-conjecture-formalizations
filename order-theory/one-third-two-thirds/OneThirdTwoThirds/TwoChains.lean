import OneThirdTwoThirds.ParallelSum
import Mathlib.Tactic.Linarith

/-!
# The 1/3–2/3 conjecture — the two-chains kernel (series-parallel)

The ordinal-sum (`OrdinalSum`) and disjoint-union (`ParallelSum`) reductions
together reduce the conjecture for **series-parallel** posets to a single
residual case: *the disjoint union of two chains `C_m ⊔ C_n` has a balanced
(cross) pair.*  (A series-parallel poset is built from singletons by series `⊕`
and parallel `⊔`; the ordinal-sum reduction handles every series node and the
disjoint-union reduction handles every parallel node whose summands are not both
chains — leaving exactly `chain ⊔ chain`.)

This file isolates the **discrete intermediate-value** mechanism at the heart of
that residual case, as a self-contained, reusable lemma
(`balanced_of_monotone_steps`).

## The mechanism

For two chains `a₀<⋯<a_{m-1}` and `b₀<⋯<b_{n-1}`, a linear extension is a
*shuffle*, so `e = C(m+n,m)` and the cross-`δ`

```
δ(aᵢ < bⱼ) = e(C_m ⊔ C_n, aᵢ<bⱼ) / e(C_m ⊔ C_n)
```

is an explicit hypergeometric quantity.  Computation (`research/explore_two_chains.py`,
all `m,n ≤ 30`) shows:

* `δ(a₀,b₀) = m/(m+n)`, `δ(a_{m-1},b_{n-1}) = n/(m+n)`;
* along the `a₀`-row `j ↦ δ(a₀,bⱼ)` (increasing) and the `b_{n-1}`-column
  `i ↦ δ(aᵢ,b_{n-1})` (decreasing), consecutive values differ by **at most 1/3**
  (the bound is attained, e.g. at `(m,n)=(1,2)`);
* hence the **first crossing** of `1/3` is automatically `≤ 2/3` — a balanced
  pair — and the appropriate path always reaches across.

The lemma below is exactly that first-crossing argument, phrased fraction-free
over a common denominator `D = e` with numerators `d k = e(·, ·<·)`: a step of at
most `D/3` cannot jump over the band `[D/3, 2D/3]`, so the first numerator with
`3·d k ≥ D` already has `3·d k ≤ 2D`.  Notably **no monotonicity** of `d` is
needed — only the step bound and the two endpoints.

What remains to turn this into a full proof of the series-parallel theorem (i.e.
to discharge the `hcross` hypothesis of `oneThirdTwoThirdsFor_par`) is the
*counting* input: the closed form of the cross before-count
`e(C_m ⊔ C_n, aᵢ<bⱼ)` and the binomial step bound
`3·C(m+n-2, m-1) ≤ C(m+n, m)` (equivalently `(m+n)(m+n-1) ≥ 3mn`), which feed
`balanced_of_monotone_steps`.  That counting is deferred.  `sorry`-free.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

/-- **Discrete intermediate value / first-crossing.**  Let `d : ℕ → ℕ` be a
sequence of before-counts over a common denominator `D` (think `d k = e(P, ·<·)`
for the `k`-th candidate pair and `D = e(P)`).  If every consecutive step is at
most a third of `D` (`3·d (k+1) ≤ 3·d k + D`), the start is at most two-thirds
(`3·d 0 ≤ 2D`), and some index `N` reaches at least a third (`D ≤ 3·d N`), then
**some index is balanced**: `D ≤ 3·d k ≤ 2D`, i.e. `δ = d k / D ∈ [1/3, 2/3]`.

The witness is the *first* index whose value reaches `D/3`; the step bound
guarantees it has not already overshot `2D/3`.  No monotonicity is required. -/
theorem balanced_of_monotone_steps {D N : ℕ} (d : ℕ → ℕ)
    (hstep : ∀ k, k < N → 3 * d (k + 1) ≤ 3 * d k + D)
    (hstart : 3 * d 0 ≤ 2 * D) (hend : D ≤ 3 * d N) :
    ∃ k, k ≤ N ∧ D ≤ 3 * d k ∧ 3 * d k ≤ 2 * D := by
  classical
  have hex : ∃ k, D ≤ 3 * d k := ⟨N, hend⟩
  have hfle : Nat.find hex ≤ N := Nat.find_le hend
  refine ⟨Nat.find hex, hfle, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; exact hstart
  · -- the predecessor falls short of `D/3`, so one step lands below `2D/3`
    have hmin : ¬ (D ≤ 3 * d (Nat.find hex - 1)) := Nat.find_min hex (by omega)
    have hs := hstep (Nat.find hex - 1) (by omega)
    have hfe : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hfe] at hs
    omega

/-- The pair-selection regime split used by the two-chains argument: the
`a₀`-row is used when `δ(a₀,b₀) = m/(m+n) ≤ 2/3` (`m ≤ 2n`), otherwise the
`b_{n-1}`-column is used (`m > 2n`).  Recorded as the trichotomy that decides
which endpoint hypothesis of `balanced_of_monotone_steps` holds at `k = 0`. -/
theorem row_or_col (m n : ℕ) : m ≤ 2 * n ∨ 2 * n < m := by omega

/-- The binomial **step bound** the counting layer must supply,
`(m+n)·(m+n-1) ≥ 3·m·n`, recorded in its subtraction-free arithmetic core
`3mn + (m+n) ≤ (m+n)²` and proved here for all `m, n ≥ 1` with `m + n ≥ 3` (the
excluded `m = n = 1` is the trivial chain with no interior step).  It is exactly
the inequality `3·C(m+n-2, m-1) ≤ C(m+n, m)` that bounds a single `a₀`-row step
by `1/3`, ready to feed `hstep` of `balanced_of_monotone_steps` once the cross
before-count is in closed form. -/
theorem step_bound_arith {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : 3 ≤ m + n) :
    3 * m * n + (m + n) ≤ (m + n) * (m + n) := by
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    have hn2 : 2 ≤ n := by omega
    nlinarith [hn2]
  · rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · obtain rfl : n = 1 := by omega
      have hm2' : 2 ≤ m := by omega
      nlinarith [hm2']
    · have hmn : m + n ≤ m * n := Nat.add_le_mul hm2 hn2
      have amgm : 2 * (m * n) ≤ m * m + n * n := by
        rcases le_total m n with hle | hle
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
          nlinarith [Nat.zero_le d]
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
          nlinarith [Nat.zero_le d]
      nlinarith [hmn, amgm]

end OneThirdTwoThirds
