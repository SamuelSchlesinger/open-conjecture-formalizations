import Fortune.CertifiedRange

namespace Fortune

/-- Verified finite range of Fortune's conjecture. -/
theorem fortune_conjecture_one_to_twelve {n : Nat}
    (hn1 : 1 ≤ n) (hn12 : n ≤ 12) :
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  exact hasPrimeLeastFortunateOffset_one_to_twelve hn1 hn12

/-- Verified finite range of Fortune's conjecture. -/
theorem fortune_conjecture_one_to_fifteen {n : Nat}
    (hn1 : 1 ≤ n) (hn15 : n ≤ 15) :
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  exact hasPrimeLeastFortunateOffset_one_to_fifteen hn1 hn15

/-- Verified finite range of Fortune's conjecture. -/
theorem fortune_conjecture_one_to_sixteen {n : Nat}
    (hn1 : 1 ≤ n) (hn16 : n ≤ 16) :
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  exact hasPrimeLeastFortunateOffset_one_to_sixteen hn1 hn16

/-- Verified finite range of Fortune's conjecture. -/
theorem fortune_conjecture_one_to_seventeen {n : Nat}
    (hn1 : 1 ≤ n) (hn17 : n ≤ 17) :
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  exact hasPrimeLeastFortunateOffset_one_to_seventeen hn1 hn17

/-- Fortune's conjecture: each least Fortunate offset is prime. -/
theorem fortune_conjecture : FortuneConjecture := by
  intro n hn
  sorry

/-- Expanded form of `fortune_conjecture`. -/
theorem fortune_conjecture_expanded :
    ∀ n : Nat, 1 ≤ n → ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  exact fortune_conjecture

end Fortune
