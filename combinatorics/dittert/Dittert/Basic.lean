import Dittert.Defs
import Mathlib.Tactic

namespace Dittert

theorem uniformEntry_zero : uniformEntry 0 = 0 := by
  simp [uniformEntry]

theorem uniformEntry_one : uniformEntry 1 = 1 := by
  simp [uniformEntry]

theorem uniformMatrix_one_eq_one :
    uniformMatrix 1 = fun _ _ => (1 : ℝ) := by
  ext i j
  simp [uniformMatrix, uniformEntry]

theorem inKn_uniform_one : InKn 1 (uniformMatrix 1) := by
  constructor
  · intro i j
    simp [uniformMatrix, uniformEntry]
  · simp [uniformMatrix, uniformEntry]

theorem matrix_eq_uniform_of_inKn_one {A : Matrix (Fin 1) (Fin 1) ℝ}
    (hA : InKn 1 A) :
    A = uniformMatrix 1 := by
  ext i j
  have h00 : A 0 0 = (1 : ℝ) := by
    simpa using hA.2
  fin_cases i
  fin_cases j
  simpa [uniformMatrix, uniformEntry] using h00

theorem dittertFunctional_uniform_one :
    dittertFunctional (uniformMatrix 1) = (1 : ℝ) := by
  simp [dittertFunctional, rowSumsProduct, colSumsProduct, uniformMatrix, uniformEntry]

end Dittert
