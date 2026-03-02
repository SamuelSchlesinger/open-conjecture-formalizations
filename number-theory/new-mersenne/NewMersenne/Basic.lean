import NewMersenne.Defs

namespace NewMersenne

theorem inNewMersenneShape_three : InNewMersenneShape 3 := by
  left
  exact ⟨2, by decide⟩

theorem inNewMersenneShape_five : InNewMersenneShape 5 := by
  right
  left
  exact ⟨2, by decide⟩

theorem inNewMersenneShape_seven : InNewMersenneShape 7 := by
  left
  exact ⟨3, by decide⟩

theorem isMersennePrimeExponent_three : IsMersennePrimeExponent 3 := by
  decide

theorem isMersennePrimeExponent_five : IsMersennePrimeExponent 5 := by
  decide

theorem isMersennePrimeExponent_seven : IsMersennePrimeExponent 7 := by
  decide

theorem isWagstaffPrimeExponent_three : IsWagstaffPrimeExponent 3 := by
  decide

theorem isWagstaffPrimeExponent_five : IsWagstaffPrimeExponent 5 := by
  decide

theorem isWagstaffPrimeExponent_seven : IsWagstaffPrimeExponent 7 := by
  decide

theorem allThreeConditions_three :
    InNewMersenneShape 3 ∧ IsMersennePrimeExponent 3 ∧ IsWagstaffPrimeExponent 3 := by
  exact ⟨inNewMersenneShape_three, isMersennePrimeExponent_three, isWagstaffPrimeExponent_three⟩

theorem allThreeConditions_five :
    InNewMersenneShape 5 ∧ IsMersennePrimeExponent 5 ∧ IsWagstaffPrimeExponent 5 := by
  exact ⟨inNewMersenneShape_five, isMersennePrimeExponent_five, isWagstaffPrimeExponent_five⟩

theorem allThreeConditions_seven :
    InNewMersenneShape 7 ∧ IsMersennePrimeExponent 7 ∧ IsWagstaffPrimeExponent 7 := by
  exact ⟨inNewMersenneShape_seven, isMersennePrimeExponent_seven, isWagstaffPrimeExponent_seven⟩

end NewMersenne
