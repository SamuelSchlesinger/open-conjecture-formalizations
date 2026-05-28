import Frankl.Entropy
import Mathlib.Tactic

/-!
# Total Correlation for Finite Boolean Laws

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file gives the finite Boolean-vector definitions needed for the
entropy-accounting side of the coupled-kernel program.  A law is represented
by weights on all finite subsets of a finite coordinate type.
-/

set_option autoImplicit false

namespace Frankl

open scoped BigOperators

/-- A finitely supported law on Boolean vectors over a finite coordinate type,
represented as weights on `Finset α`. -/
structure FiniteBoolLaw (α : Type*) [Fintype α] [DecidableEq α] where
  weight : Finset α → ℝ
  nonneg : ∀ A, 0 ≤ weight A
  total : ∑ A : Finset α, weight A = 1

namespace FiniteBoolLaw

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Shannon entropy of a finite Boolean law, using natural logarithms. -/
noncomputable def entropy (P : FiniteBoolLaw α) : ℝ :=
  ∑ A : Finset α, -P.weight A * Real.log (P.weight A)

/-- Marginal probability that coordinate `x` is present. -/
noncomputable def coordMarginal (P : FiniteBoolLaw α) (x : α) : ℝ :=
  ∑ A : Finset α, P.weight A * (if x ∈ A then 1 else 0)

/-- Sum of binary entropies of the coordinate marginals. -/
noncomputable def coordinateEntropySum (P : FiniteBoolLaw α) : ℝ :=
  ∑ x : α, binaryEntropy (P.coordMarginal x)

/-- Total correlation, `sum_i h(p_i) - H(P)`. -/
noncomputable def totalCorrelation (P : FiniteBoolLaw α) : ℝ :=
  P.coordinateEntropySum - P.entropy

/-- The chain identity is definitional with this normalization. -/
theorem entropy_eq_coordinateEntropySum_sub_totalCorrelation
    (P : FiniteBoolLaw α) :
    P.entropy = P.coordinateEntropySum - P.totalCorrelation := by
  unfold totalCorrelation
  ring

end FiniteBoolLaw

end Frankl
