import Dittert.Defs

namespace Dittert

/-- Dittert conjecture (global form). -/
theorem dittert_conjecture : DittertConjecture := by
  intro n
  sorry

/-- Expanded size-by-size form of `dittert_conjecture`. -/
theorem dittert_conjecture_expanded :
    ∀ n : Nat, n > 0 →
      ∀ A : Matrix (Fin n) (Fin n) ℝ, InKn n A →
        dittertFunctional A ≤ dittertFunctional (uniformMatrix n) ∧
        (dittertFunctional A = dittertFunctional (uniformMatrix n) → A = uniformMatrix n) := by
  intro n
  exact dittert_conjecture n

end Dittert
