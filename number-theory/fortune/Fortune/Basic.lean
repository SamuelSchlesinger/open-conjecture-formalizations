import Fortune.Defs
import Mathlib.Tactic

namespace Fortune

theorem nthPrimorial_zero : nthPrimorial 0 = 1 := by
  simp [nthPrimorial]

theorem nthPrimorial_one : nthPrimorial 1 = 2 := by
  simp [nthPrimorial, nthPrime]

theorem nthPrimorial_two : nthPrimorial 2 = 6 := by
  rw [nthPrimorial]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_one]
  simp [nthPrime]

theorem nthPrimorial_three : nthPrimorial 3 = 30 := by
  rw [nthPrimorial]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_one]
  simp [nthPrime]

theorem nthPrimorial_four : nthPrimorial 4 = 210 := by
  rw [nthPrimorial]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_one]
  simp [nthPrime]

theorem isLeastFortunateOffset_one : IsLeastFortunateOffset 1 3 := by
  constructor
  · simpa [IsFortunateOffset, nthPrimorial_one] using
      (by norm_num : 1 < 3 ∧ Nat.Prime (2 + 3))
  · intro k hk1 hk2
    have hkLow : 2 ≤ k := Nat.succ_le_of_lt hk1
    have hkHigh : k ≤ 2 := Nat.le_pred_of_lt hk2
    have hk : k = 2 := Nat.le_antisymm hkHigh hkLow
    subst hk
    simpa [nthPrimorial_one] using (by norm_num : ¬Nat.Prime (2 + 2))

theorem isLeastFortunateOffset_two : IsLeastFortunateOffset 2 5 := by
  constructor
  · simpa [IsFortunateOffset, nthPrimorial_two] using
      (by norm_num : 1 < 5 ∧ Nat.Prime (6 + 5))
  · intro k hk1 hk2
    have hkLow : 2 ≤ k := Nat.succ_le_of_lt hk1
    have hkHigh : k ≤ 4 := Nat.le_pred_of_lt hk2
    interval_cases k
    · simpa [nthPrimorial_two] using (by norm_num : ¬Nat.Prime (6 + 2))
    · simpa [nthPrimorial_two] using (by norm_num : ¬Nat.Prime (6 + 3))
    · simpa [nthPrimorial_two] using (by norm_num : ¬Nat.Prime (6 + 4))

theorem isLeastFortunateOffset_three : IsLeastFortunateOffset 3 7 := by
  constructor
  · simpa [IsFortunateOffset, nthPrimorial_three] using
      (by norm_num : 1 < 7 ∧ Nat.Prime (30 + 7))
  · intro k hk1 hk2
    have hkLow : 2 ≤ k := Nat.succ_le_of_lt hk1
    have hkHigh : k ≤ 6 := Nat.le_pred_of_lt hk2
    interval_cases k
    · simpa [nthPrimorial_three] using (by norm_num : ¬Nat.Prime (30 + 2))
    · simpa [nthPrimorial_three] using (by norm_num : ¬Nat.Prime (30 + 3))
    · simpa [nthPrimorial_three] using (by norm_num : ¬Nat.Prime (30 + 4))
    · simpa [nthPrimorial_three] using (by norm_num : ¬Nat.Prime (30 + 5))
    · simpa [nthPrimorial_three] using (by norm_num : ¬Nat.Prime (30 + 6))

theorem isLeastFortunateOffset_four : IsLeastFortunateOffset 4 13 := by
  constructor
  · simpa [IsFortunateOffset, nthPrimorial_four] using
      (by norm_num : 1 < 13 ∧ Nat.Prime (210 + 13))
  · intro k hk1 hk2
    have hkLow : 2 ≤ k := Nat.succ_le_of_lt hk1
    have hkHigh : k ≤ 12 := Nat.le_pred_of_lt hk2
    interval_cases k
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 2))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 3))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 4))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 5))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 6))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 7))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 8))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 9))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 10))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 11))
    · simpa [nthPrimorial_four] using (by norm_num : ¬Nat.Prime (210 + 12))

theorem hasPrimeLeastFortunateOffset_one :
    ∃ m : Nat, IsLeastFortunateOffset 1 m ∧ Nat.Prime m := by
  exact ⟨3, isLeastFortunateOffset_one, by norm_num⟩

theorem hasPrimeLeastFortunateOffset_two :
    ∃ m : Nat, IsLeastFortunateOffset 2 m ∧ Nat.Prime m := by
  exact ⟨5, isLeastFortunateOffset_two, by norm_num⟩

theorem hasPrimeLeastFortunateOffset_three :
    ∃ m : Nat, IsLeastFortunateOffset 3 m ∧ Nat.Prime m := by
  exact ⟨7, isLeastFortunateOffset_three, by norm_num⟩

theorem hasPrimeLeastFortunateOffset_four :
    ∃ m : Nat, IsLeastFortunateOffset 4 m ∧ Nat.Prime m := by
  exact ⟨13, isLeastFortunateOffset_four, by norm_num⟩

end Fortune
