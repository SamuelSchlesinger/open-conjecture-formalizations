import CatalanMersenne.Basic
import Mathlib.Tactic.IntervalCases

namespace CatalanMersenne

theorem isCatalanMersennePrime_zero_to_three {n : Nat} (hn : n ≤ 3) :
    IsCatalanMersennePrime n := by
  interval_cases n
  · exact isCatalanMersennePrime_zero
  · exact isCatalanMersennePrime_one
  · exact isCatalanMersennePrime_two
  · exact isCatalanMersennePrime_three

theorem initialPrimeBlock_exists :
    ∃ N : Nat, ∀ n : Nat, n ≤ N → IsCatalanMersennePrime n := by
  refine ⟨3, ?_⟩
  intro n hn
  exact isCatalanMersennePrime_zero_to_three hn

end CatalanMersenne
