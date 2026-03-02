import Dittert.Basic

namespace Dittert

theorem dittertConjectureAt_one : DittertConjectureAt 1 := by
  intro hn A hA
  have hEq : A = uniformMatrix 1 := matrix_eq_uniform_of_inKn_one hA
  constructor
  · simpa [hEq] using (le_rfl : dittertFunctional (uniformMatrix 1) ≤ dittertFunctional (uniformMatrix 1))
  · intro _
    exact hEq

end Dittert
