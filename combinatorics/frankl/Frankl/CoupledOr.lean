import Mathlib.Tactic

/-!
# One-Coordinate Coupled OR Algebra

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file formalizes the algebraic core behind the coupled-OR entropy probe.
For one Bernoulli coordinate with marginal `p`, a symmetric coupling is
determined by the intersection mass `r = P(X_i = 1, Y_i = 1)`.  The OR
marginal is then `2 * p - r`.  Thus, in the light-coordinate regime, coupling
can move the OR marginal through the whole Frechet interval instead of being
stuck at the independent value `2 * p - p ^ 2`.
-/

set_option autoImplicit false

namespace Frankl

/-- The one-coordinate OR marginal obtained from marginal `p` and intersection
mass `r`. -/
def oneCoordOrMarginal (p r : ℝ) : ℝ :=
  2 * p - r

/-- The intersection mass that would realize a requested one-coordinate OR
target `q`. -/
def targetIntersectionMass (p q : ℝ) : ℝ :=
  2 * p - q

/-- The intersection mass that centers the one-coordinate OR marginal at
`1 / 2`. -/
noncomputable def centeredIntersectionMass (p : ℝ) : ℝ :=
  targetIntersectionMass p (1 / 2)

theorem oneCoordOrMarginal_targetIntersectionMass (p q : ℝ) :
    oneCoordOrMarginal p (targetIntersectionMass p q) = q := by
  simp [oneCoordOrMarginal, targetIntersectionMass]

theorem targetIntersectionMass_nonneg {p q : ℝ} (hq : q ≤ 2 * p) :
    0 ≤ targetIntersectionMass p q := by
  simp [targetIntersectionMass]
  linarith

theorem targetIntersectionMass_le_marginal {p q : ℝ} (hpq : p ≤ q) :
    targetIntersectionMass p q ≤ p := by
  simp [targetIntersectionMass]
  linarith

theorem targetIntersectionMass_ge_frechetLower {p q : ℝ} (hq : q ≤ 1) :
    2 * p - 1 ≤ targetIntersectionMass p q := by
  simp [targetIntersectionMass]
  linarith

/-- A target `q` between `p` and `2p`, and at most `1`, is realized by a
Frechet-feasible one-coordinate coupling. -/
theorem targetIntersectionMass_feasible {p q : ℝ}
    (hpq : p ≤ q) (hq2 : q ≤ 2 * p) (hq1 : q ≤ 1) :
    2 * p - 1 ≤ targetIntersectionMass p q ∧
      0 ≤ targetIntersectionMass p q ∧
      targetIntersectionMass p q ≤ p ∧
      oneCoordOrMarginal p (targetIntersectionMass p q) = q := by
  exact ⟨targetIntersectionMass_ge_frechetLower hq1,
    targetIntersectionMass_nonneg hq2,
    targetIntersectionMass_le_marginal hpq,
    oneCoordOrMarginal_targetIntersectionMass p q⟩

theorem centeredIntersectionMass_nonneg {p : ℝ} (hp : (1 / 4 : ℝ) ≤ p) :
    0 ≤ centeredIntersectionMass p := by
  simp [centeredIntersectionMass, targetIntersectionMass]
  linarith

theorem centeredIntersectionMass_le_marginal {p : ℝ} (hp : p ≤ (1 / 2 : ℝ)) :
    centeredIntersectionMass p ≤ p := by
  simp [centeredIntersectionMass, targetIntersectionMass]
  linarith

theorem centeredIntersectionMass_ge_frechetLower (p : ℝ) :
    2 * p - 1 ≤ centeredIntersectionMass p := by
  simp [centeredIntersectionMass, targetIntersectionMass]
  linarith

theorem oneCoordOrMarginal_centeredIntersectionMass (p : ℝ) :
    oneCoordOrMarginal p (centeredIntersectionMass p) = 1 / 2 := by
  simp [centeredIntersectionMass, oneCoordOrMarginal_targetIntersectionMass]

/-- Any coordinate with `1/4 ≤ p ≤ 1/2` can be centered at OR marginal `1/2`
by a Frechet-feasible one-coordinate coupling. -/
theorem centeredIntersectionMass_feasible {p : ℝ}
    (hp_low : (1 / 4 : ℝ) ≤ p) (hp_high : p ≤ (1 / 2 : ℝ)) :
    2 * p - 1 ≤ centeredIntersectionMass p ∧
      0 ≤ centeredIntersectionMass p ∧
      centeredIntersectionMass p ≤ p ∧
      oneCoordOrMarginal p (centeredIntersectionMass p) = 1 / 2 := by
  exact ⟨centeredIntersectionMass_ge_frechetLower p,
    centeredIntersectionMass_nonneg hp_low,
    centeredIntersectionMass_le_marginal hp_high,
    oneCoordOrMarginal_centeredIntersectionMass p⟩

theorem oneCoordOrMarginal_zero (p : ℝ) :
    oneCoordOrMarginal p 0 = 2 * p := by
  simp [oneCoordOrMarginal]

theorem oneCoordOrMarginal_zero_gt_marginal {p : ℝ} (hp : 0 < p) :
    p < oneCoordOrMarginal p 0 := by
  simp [oneCoordOrMarginal]
  linarith

theorem oneCoordOrMarginal_zero_lt_half {p : ℝ} (hp : p < (1 / 4 : ℝ)) :
    oneCoordOrMarginal p 0 < 1 / 2 := by
  simp [oneCoordOrMarginal]
  linarith

end Frankl
