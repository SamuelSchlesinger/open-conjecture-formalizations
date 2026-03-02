import Fortune.Defs

namespace Fortune

/-- Fortune's conjecture: each least Fortunate offset is prime. -/
theorem fortune_conjecture : FortuneConjecture := by
  intro n hn
  sorry

/-- Expanded form of `fortune_conjecture`. -/
theorem fortune_conjecture_expanded :
    ∀ n : Nat, 1 ≤ n → ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  exact fortune_conjecture

end Fortune
