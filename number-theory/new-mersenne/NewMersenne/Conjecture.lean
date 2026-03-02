import NewMersenne.Defs

namespace NewMersenne

/-- The New Mersenne conjecture for odd exponents. -/
theorem newMersenne_conjecture : NewMersenneConjecture := by
  intro p hp
  sorry

/-- Expanded form of `newMersenne_conjecture`. -/
theorem newMersenne_conjecture_expanded :
    ∀ p : Nat, Odd p →
      ((InNewMersenneShape p ∧ IsMersennePrimeExponent p) → IsWagstaffPrimeExponent p) ∧
      ((InNewMersenneShape p ∧ IsWagstaffPrimeExponent p) → IsMersennePrimeExponent p) ∧
      ((IsMersennePrimeExponent p ∧ IsWagstaffPrimeExponent p) → InNewMersenneShape p) := by
  exact newMersenne_conjecture

end NewMersenne
