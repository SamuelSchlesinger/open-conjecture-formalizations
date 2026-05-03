import Frankl.Defs

set_option autoImplicit false

namespace Frankl

/-- Frankl's union-closed sets conjecture. -/
theorem frankl_conjecture : FranklConjecture := by
  intro α hα F hClosed hNonempty
  sorry

/-- Expanded form of `frankl_conjecture`. -/
theorem frankl_conjecture_expanded :
    ∀ {α : Type} [DecidableEq α], ∀ F : Finset (Finset α),
      IsUnionClosed F → HasNonemptyMember F → ∃ x : α, IsFranklElement x F := by
  exact frankl_conjecture

end Frankl
