import NewMersenne.Basic

namespace NewMersenne

theorem allThreeConditions_of_eq_three_five_seven {p : Nat}
    (hp : p = 3 ∨ p = 5 ∨ p = 7) :
    InNewMersenneShape p ∧ IsMersennePrimeExponent p ∧ IsWagstaffPrimeExponent p := by
  rcases hp with rfl | rfl | rfl
  · exact allThreeConditions_three
  · exact allThreeConditions_five
  · exact allThreeConditions_seven

theorem newMersenneConjecture_holds_for_three_five_seven {p : Nat}
    (hp : p = 3 ∨ p = 5 ∨ p = 7) :
    ((InNewMersenneShape p ∧ IsMersennePrimeExponent p) → IsWagstaffPrimeExponent p) ∧
    ((InNewMersenneShape p ∧ IsWagstaffPrimeExponent p) → IsMersennePrimeExponent p) ∧
    ((IsMersennePrimeExponent p ∧ IsWagstaffPrimeExponent p) → InNewMersenneShape p) := by
  rcases allThreeConditions_of_eq_three_five_seven hp with ⟨hA, hB, hC⟩
  constructor
  · intro _
    exact hC
  constructor
  · intro _
    exact hB
  · intro _
    exact hA

end NewMersenne
