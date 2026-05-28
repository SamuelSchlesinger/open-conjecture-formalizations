import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-!
# Binary Entropy Lemmas

Reference: `combinatorics/frankl/research/checklist.md`

This file records the small binary-entropy facts needed by the coupled-OR
program.  Mathlib already contains the main analytic theorem:
`Real.binEntropy` is strictly increasing on `[0, 1 / 2]` and symmetric about
`1 / 2`.
-/

set_option autoImplicit false

namespace Frankl

/-- Local alias for Mathlib's binary entropy function. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  Real.binEntropy p

theorem binaryEntropy_symm (p : ℝ) :
    binaryEntropy (1 - p) = binaryEntropy p := by
  simp [binaryEntropy]

theorem binaryEntropy_strictMonoOn_Icc_zero_half :
    StrictMonoOn binaryEntropy (Set.Icc (0 : ℝ) (2⁻¹ : ℝ)) := by
  intro x hx y hy hxy
  simpa [binaryEntropy] using Real.binEntropy_strictMonoOn hx hy hxy

/-- Moving a Bernoulli marginal upward while staying before the symmetric
point `1 - p` strictly increases binary entropy. -/
theorem binaryEntropy_lt_of_lt_of_lt_one_sub {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p < q) (hq : q < 1 - p) :
    binaryEntropy p < binaryEntropy q := by
  by_cases hq_half : q ≤ (2⁻¹ : ℝ)
  · have hp_half : p ≤ (1 / 2 : ℝ) := by linarith
    have hp_mem : p ∈ Set.Icc (0 : ℝ) (2⁻¹ : ℝ) := by
      constructor
      · exact hp0
      · rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]
        exact hp_half
    exact binaryEntropy_strictMonoOn_Icc_zero_half
      hp_mem ⟨by linarith, hq_half⟩ hpq
  · have hhalfq_inv : (2⁻¹ : ℝ) ≤ q := le_of_not_ge hq_half
    have hhalfq : (1 / 2 : ℝ) ≤ q := by
      rw [← show (2⁻¹ : ℝ) = 1 / 2 by norm_num]
      exact hhalfq_inv
    have hp_half : p ≤ (1 / 2 : ℝ) := by linarith
    have hq_lt_one : q < 1 := by linarith
    have hp_one_sub_q : p < 1 - q := by linarith
    have h_one_sub_q_half : 1 - q ≤ (1 / 2 : ℝ) := by linarith
    have hp_mem : p ∈ Set.Icc (0 : ℝ) (2⁻¹ : ℝ) := by
      constructor
      · exact hp0
      · rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]
        exact hp_half
    have h_one_sub_q_mem : 1 - q ∈ Set.Icc (0 : ℝ) (2⁻¹ : ℝ) := by
      constructor
      · linarith
      · rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]
        exact h_one_sub_q_half
    calc
      binaryEntropy p < binaryEntropy (1 - q) :=
        binaryEntropy_strictMonoOn_Icc_zero_half
          hp_mem
          h_one_sub_q_mem
          hp_one_sub_q
      _ = binaryEntropy q := binaryEntropy_symm q

/-- Coupled-OR entropy gain in the critical centered regime. -/
theorem binaryEntropy_lt_half_of_lt_half {p : ℝ}
    (hp0 : 0 ≤ p) (hp_half : p < (1 / 2 : ℝ)) :
    binaryEntropy p < binaryEntropy (1 / 2 : ℝ) := by
  have hq : (1 / 2 : ℝ) < 1 - p := by linarith
  exact binaryEntropy_lt_of_lt_of_lt_one_sub hp0 hp_half hq

/-- Rare positive coordinates gain entropy when boosted to their maximal
one-coordinate OR marginal `2p`. -/
theorem binaryEntropy_lt_two_mul_of_pos_lt_quarter {p : ℝ}
    (hp_pos : 0 < p) (hp_quarter : p < (1 / 4 : ℝ)) :
    binaryEntropy p < binaryEntropy (2 * p) := by
  have hp0 : 0 ≤ p := hp_pos.le
  have hp_two : p < 2 * p := by linarith
  have htwo_lt : 2 * p < 1 - p := by linarith
  exact binaryEntropy_lt_of_lt_of_lt_one_sub hp0 hp_two htwo_lt

end Frankl
