import Frankl.Entropy
import Mathlib.Tactic

/-!
# AHS Hinge Formulae

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file defines the real-valued functions used in the
Alweiss-Huang-Sellke one-variable hinge.  Later certificate files should prove
interval lower bounds for these functions and connect them to the AHS
inequality.
-/

set_option autoImplicit false

namespace Frankl

/-- The golden-ratio conjugate used by Alweiss-Huang-Sellke. -/
noncomputable def ahsPhi : ℝ :=
  (Real.sqrt 5 - 1) / 2

/-- The AHS one-variable hinge expression `phi * h(x^2) - x * h(x)`. -/
noncomputable def ahsG (x : ℝ) : ℝ :=
  ahsPhi * binaryEntropy (x ^ 2) - x * binaryEntropy x

/-- Left side of the AHS middle-interval monotone chain. -/
noncomputable def ahsG1 (x : ℝ) : ℝ :=
  ahsPhi * binaryEntropy (x ^ 2)

/-- Right side of the AHS middle-interval monotone chain. -/
noncomputable def ahsG2 (x : ℝ) : ℝ :=
  x * binaryEntropy x

/-- The numerator `(1 - x^2) * G''(x)` used in the AHS `I1` convexity table,
written in the closed form audited by `gilmer_ahs_verification.py`. -/
noncomputable def ahsL (x : ℝ) : ℝ :=
  2 * ahsPhi * (1 - x ^ 2) * Real.log ((x ^ 2)⁻¹ - 1)
    - 4 * ahsPhi
    - 2 * x ^ 2 * Real.log x
    + 2 * (x ^ 2 - 1) * Real.log (1 - x)
    + x
    + 2 * Real.log x
    + 1

theorem ahsG_eq (x : ℝ) :
    ahsG x = ahsPhi * binaryEntropy (x ^ 2) - x * binaryEntropy x := by
  rfl

theorem ahsG_eq_g1_sub_g2 (x : ℝ) :
    ahsG x = ahsG1 x - ahsG2 x := by
  rfl

end Frankl
