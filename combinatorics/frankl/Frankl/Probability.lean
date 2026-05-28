import Frankl.CoupledOr
import Mathlib.Tactic

/-!
# Finite Probability Fragments

Reference: `combinatorics/frankl/research/checklist.md`

This file keeps the first probability layer deliberately small.  A coupling of
two Bernoulli coordinates is represented by its four atom masses.  This is
enough to restate the one-coordinate coupled-OR algebra as an actual finite
probability construction, without importing a larger probability API yet.
-/

set_option autoImplicit false

namespace Frankl

/-- A finite coupling of two Bernoulli coordinates, stored as the four atom
masses `P(0,0)`, `P(0,1)`, `P(1,0)`, and `P(1,1)`. -/
structure TwoBernoulliCoupling where
  p00 : ℝ
  p01 : ℝ
  p10 : ℝ
  p11 : ℝ
  p00_nonneg : 0 ≤ p00
  p01_nonneg : 0 ≤ p01
  p10_nonneg : 0 ≤ p10
  p11_nonneg : 0 ≤ p11
  total : p00 + p01 + p10 + p11 = 1

namespace TwoBernoulliCoupling

/-- The marginal probability that the left Bernoulli coordinate is `1`. -/
def leftMarginal (c : TwoBernoulliCoupling) : ℝ :=
  c.p10 + c.p11

/-- The marginal probability that the right Bernoulli coordinate is `1`. -/
def rightMarginal (c : TwoBernoulliCoupling) : ℝ :=
  c.p01 + c.p11

/-- The intersection mass `P(X = 1, Y = 1)`. -/
def intersectionMass (c : TwoBernoulliCoupling) : ℝ :=
  c.p11

/-- The OR marginal `P(X ∨ Y = 1)`. -/
def orMarginal (c : TwoBernoulliCoupling) : ℝ :=
  c.p01 + c.p10 + c.p11

theorem orMarginal_eq_left_add_right_sub_intersection
    (c : TwoBernoulliCoupling) :
    c.orMarginal = c.leftMarginal + c.rightMarginal - c.intersectionMass := by
  simp [orMarginal, leftMarginal, rightMarginal, intersectionMass]
  ring

theorem orMarginal_eq_oneCoordOrMarginal {c : TwoBernoulliCoupling} {p : ℝ}
    (hL : c.leftMarginal = p) (hR : c.rightMarginal = p) :
    c.orMarginal = oneCoordOrMarginal p c.intersectionMass := by
  calc
    c.orMarginal = c.leftMarginal + c.rightMarginal - c.intersectionMass :=
      c.orMarginal_eq_left_add_right_sub_intersection
    _ = oneCoordOrMarginal p c.intersectionMass := by
      simp [hL, hR, oneCoordOrMarginal]
      ring

/-- The explicit two-Bernoulli coupling realizing a feasible OR target `q`
from a common marginal `p`. -/
def forTarget (p q : ℝ) (hpq : p ≤ q) (hq2 : q ≤ 2 * p) (hq1 : q ≤ 1) :
    TwoBernoulliCoupling where
  p00 := 1 - q
  p01 := q - p
  p10 := q - p
  p11 := targetIntersectionMass p q
  p00_nonneg := by linarith
  p01_nonneg := by linarith
  p10_nonneg := by linarith
  p11_nonneg := targetIntersectionMass_nonneg hq2
  total := by
    simp [targetIntersectionMass]
    ring

theorem forTarget_leftMarginal (p q : ℝ)
    (hpq : p ≤ q) (hq2 : q ≤ 2 * p) (hq1 : q ≤ 1) :
    (forTarget p q hpq hq2 hq1).leftMarginal = p := by
  simp [forTarget, leftMarginal, targetIntersectionMass]
  ring

theorem forTarget_rightMarginal (p q : ℝ)
    (hpq : p ≤ q) (hq2 : q ≤ 2 * p) (hq1 : q ≤ 1) :
    (forTarget p q hpq hq2 hq1).rightMarginal = p := by
  simp [forTarget, rightMarginal, targetIntersectionMass]
  ring

theorem forTarget_intersectionMass (p q : ℝ)
    (hpq : p ≤ q) (hq2 : q ≤ 2 * p) (hq1 : q ≤ 1) :
    (forTarget p q hpq hq2 hq1).intersectionMass =
      targetIntersectionMass p q := by
  rfl

theorem forTarget_orMarginal (p q : ℝ)
    (hpq : p ≤ q) (hq2 : q ≤ 2 * p) (hq1 : q ≤ 1) :
    (forTarget p q hpq hq2 hq1).orMarginal = q := by
  simp [forTarget, orMarginal, targetIntersectionMass]
  ring

/-- Finite-probability form of the one-coordinate coupled-OR window: every
target `q` in the feasible interval is realized by an explicit coupling with
both marginals equal to `p`. -/
theorem exists_coupling_for_orTarget {p q : ℝ}
    (hpq : p ≤ q) (hq2 : q ≤ 2 * p) (hq1 : q ≤ 1) :
    ∃ c : TwoBernoulliCoupling,
      c.leftMarginal = p ∧
        c.rightMarginal = p ∧
        c.orMarginal = q ∧
        c.intersectionMass = targetIntersectionMass p q := by
  refine ⟨forTarget p q hpq hq2 hq1, ?_⟩
  exact ⟨forTarget_leftMarginal p q hpq hq2 hq1,
    forTarget_rightMarginal p q hpq hq2 hq1,
    forTarget_orMarginal p q hpq hq2 hq1,
    forTarget_intersectionMass p q hpq hq2 hq1⟩

/-- Critical light coordinates can be centered by an explicit two-Bernoulli
coupling. -/
theorem exists_centered_coupling {p : ℝ}
    (hp_low : (1 / 4 : ℝ) ≤ p) (hp_high : p ≤ (1 / 2 : ℝ)) :
    ∃ c : TwoBernoulliCoupling,
      c.leftMarginal = p ∧
        c.rightMarginal = p ∧
        c.orMarginal = 1 / 2 ∧
        c.intersectionMass = centeredIntersectionMass p := by
  have hpq : p ≤ (1 / 2 : ℝ) := hp_high
  have hq2 : (1 / 2 : ℝ) ≤ 2 * p := by linarith
  have hq1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  rcases exists_coupling_for_orTarget hpq hq2 hq1 with
    ⟨c, hL, hR, hOr, hInter⟩
  refine ⟨c, hL, hR, hOr, ?_⟩
  simpa [centeredIntersectionMass] using hInter

/-- Rare coordinates can be boosted to OR marginal `2p` by taking zero
intersection mass. -/
theorem exists_double_or_coupling {p : ℝ}
    (hp0 : 0 ≤ p) (hp_half : p ≤ (1 / 2 : ℝ)) :
    ∃ c : TwoBernoulliCoupling,
      c.leftMarginal = p ∧
        c.rightMarginal = p ∧
        c.orMarginal = 2 * p ∧
        c.intersectionMass = 0 := by
  have hpq : p ≤ 2 * p := by linarith
  have hq2 : 2 * p ≤ 2 * p := le_rfl
  have hq1 : 2 * p ≤ 1 := by linarith
  rcases exists_coupling_for_orTarget hpq hq2 hq1 with
    ⟨c, hL, hR, hOr, hInter⟩
  refine ⟨c, hL, hR, hOr, ?_⟩
  simpa [targetIntersectionMass] using hInter

end TwoBernoulliCoupling

end Frankl
