import Frankl.Entropy
import Mathlib.Tactic

/-!
# Frechet-Kernel Coupled Hinge

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file names the finite object suggested by the Gilmer/AHS comparison.
The AHS product hinge uses the conditional zero-zero mass `x * y`.  A genuinely
coupled hinge may instead choose any Frechet-feasible zero-zero mass
`t ∈ [max(0, x + y - 1), min(x, y)]` for each pair of histories.
-/

set_option autoImplicit false

namespace Frankl

open scoped BigOperators

/-- Lower Frechet bound for a zero-zero mass with zero probabilities `x` and
`y`. -/
def frechetZeroLower (x y : ℝ) : ℝ :=
  max 0 (x + y - 1)

/-- Upper Frechet bound for a zero-zero mass with zero probabilities `x` and
`y`. -/
def frechetZeroUpper (x y : ℝ) : ℝ :=
  min x y

/-- A zero-zero kernel value compatible with two Bernoulli zero marginals. -/
def FrechetZeroKernel (x y t : ℝ) : Prop :=
  frechetZeroLower x y ≤ t ∧ t ≤ frechetZeroUpper x y

theorem product_frechetZeroKernel {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    FrechetZeroKernel x y (x * y) := by
  constructor
  · unfold frechetZeroLower
    refine max_le ?_ ?_
    · nlinarith [mul_nonneg hx0 hy0]
    · have hprod : 0 ≤ (1 - x) * (1 - y) :=
        mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)
      nlinarith
  · unfold frechetZeroUpper
    refine le_min ?_ ?_
    · have hprod : 0 ≤ x * (1 - y) :=
        mul_nonneg hx0 (sub_nonneg.mpr hy1)
      nlinarith
    · have hprod : 0 ≤ y * (1 - x) :=
        mul_nonneg hy0 (sub_nonneg.mpr hx1)
      nlinarith

/-- A finite Frechet-kernel hinge datum.  The type `ι` indexes histories.

`weight` is the history distribution `μ`, `plan` is a self-coupling `κ` of
that distribution, `zeroProb` assigns each history its conditional zero
probability, and `kernel` chooses a Frechet-feasible zero-zero mass for each
history pair. -/
structure FrechetKernelHinge (ι : Type*) [Fintype ι] [DecidableEq ι] where
  weight : ι → ℝ
  plan : ι → ι → ℝ
  zeroProb : ι → ℝ
  kernel : ι → ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_total : ∑ i, weight i = 1
  plan_nonneg : ∀ i j, 0 ≤ plan i j
  left_marginal : ∀ i, ∑ j, plan i j = weight i
  right_marginal : ∀ j, ∑ i, plan i j = weight j
  zeroProb_mem : ∀ i, 0 ≤ zeroProb i ∧ zeroProb i ≤ 1
  kernel_feasible : ∀ i j, FrechetZeroKernel (zeroProb i) (zeroProb j) (kernel i j)

namespace FrechetKernelHinge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The input side of the coupled hinge, `E_{x ~ μ} h(x)`. -/
noncomputable def inputEntropy (H : FrechetKernelHinge ι) : ℝ :=
  ∑ i, H.weight i * binaryEntropy (H.zeroProb i)

/-- The coupled output side of the hinge, `E_{(x,y) ~ κ} h(t(x,y))`. -/
noncomputable def outputEntropy (H : FrechetKernelHinge ι) : ℝ :=
  ∑ i, ∑ j, H.plan i j * binaryEntropy (H.kernel i j)

/-- The raw one-coordinate Frechet-kernel entropy gain. -/
noncomputable def entropyGain (H : FrechetKernelHinge ι) : ℝ :=
  H.outputEntropy - H.inputEntropy

/-- Net gain after charging a total-correlation cost.  A future global
coupling theorem needs to upper-bound this cost by the raw Frechet-kernel
gain. -/
noncomputable def netEntropyGain (H : FrechetKernelHinge ι) (totalCorrelationCost : ℝ) :
    ℝ :=
  H.entropyGain - totalCorrelationCost

theorem netEntropyGain_pos_of_cost_lt_gain (H : FrechetKernelHinge ι)
    {totalCorrelationCost : ℝ}
    (hcost : totalCorrelationCost < H.entropyGain) :
    0 < H.netEntropyGain totalCorrelationCost := by
  unfold netEntropyGain
  linarith

end FrechetKernelHinge

end Frankl
