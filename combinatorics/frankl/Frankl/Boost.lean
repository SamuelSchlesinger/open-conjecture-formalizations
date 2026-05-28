import Mathlib.Tactic

/-!
# Trace-Preserving Boost Inequality

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

The trace-preserving partial boost lemma has one combinatorial part and one
arithmetic part.  The combinatorial part constructs a permutation preserving
the negative-coordinate trace and boosting a unique positive coordinate by
`Delta`.  This file formalizes the arithmetic part: once such a boost exists,
the signed assignment inequality follows from the displayed lower bound on
`Delta`.
-/

set_option autoImplicit false

namespace Frankl

/-- Signed slack for a one-positive trace-preserving boost.

Here `lambda` is the positive weight, `p` is the positive coordinate
frequency, `Delta` is the trace-preserving boost amount, and `eta` is the
nonnegative contribution already supplied by negative coordinates kept at
their diagonal values. -/
noncomputable def onePositiveBoostSlack (lambda p Delta eta : ℝ) : ℝ :=
  lambda * (p + Delta - 1 / 2) + eta

/-- The boost threshold that makes `onePositiveBoostSlack` nonnegative. -/
noncomputable def requiredTraceBoost (lambda p eta : ℝ) : ℝ :=
  1 / 2 - p - eta / lambda

theorem onePositiveBoostSlack_nonneg_of_required_le {lambda p Delta eta : ℝ}
    (hlambda : 0 < lambda)
    (hDelta : requiredTraceBoost lambda p eta ≤ Delta) :
    0 ≤ onePositiveBoostSlack lambda p Delta eta := by
  unfold onePositiveBoostSlack requiredTraceBoost at *
  have hmul := mul_le_mul_of_nonneg_left hDelta hlambda.le
  have hne : lambda ≠ 0 := ne_of_gt hlambda
  have hrewrite : lambda * (1 / 2 - p - eta / lambda) =
      lambda * (1 / 2 - p) - eta := by
    field_simp [hne]
  rw [hrewrite] at hmul
  nlinarith

/-- Protected-block boosting is the special case `Delta = p`.  If
`1/4 <= p`, the positive coordinate already contributes nonnegative slack even
before adding the negative-coordinate contribution `eta`. -/
theorem onePositiveBoostSlack_nonneg_of_protected {lambda p eta : ℝ}
    (hlambda : 0 ≤ lambda)
    (hp : (1 / 4 : ℝ) ≤ p)
    (heta : 0 ≤ eta) :
    0 ≤ onePositiveBoostSlack lambda p p eta := by
  unfold onePositiveBoostSlack
  nlinarith [mul_nonneg hlambda (by linarith : 0 ≤ p + p - (1 / 2 : ℝ))]

end Frankl
