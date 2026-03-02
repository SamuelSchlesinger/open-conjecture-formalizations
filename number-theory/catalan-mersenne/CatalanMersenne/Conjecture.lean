import CatalanMersenne.Defs

namespace CatalanMersenne

/-- Catalan-Mersenne cutoff conjecture:
there exists a threshold after which all terms are composite. -/
theorem catalanMersenne_cutoff_conjecture :
    CatalanMersenneCutoffConjecture := by
  sorry

/-- Expanded form of `catalanMersenne_cutoff_conjecture`. -/
theorem catalanMersenne_cutoff_conjecture_expanded :
    ∃ N : Nat,
      (∀ n : Nat, n ≤ N → IsCatalanMersennePrime n) ∧
      (∀ n : Nat, N < n → ¬IsCatalanMersennePrime n) := by
  exact catalanMersenne_cutoff_conjecture

end CatalanMersenne
