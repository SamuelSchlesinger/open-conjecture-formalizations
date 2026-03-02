import Fortune.SmallCases
import Mathlib.Tactic.IntervalCases

namespace Fortune

theorem nthPrimorial_five : nthPrimorial 5 = 2310 := by
  rw [nthPrimorial]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_one]
  simp [nthPrime]

theorem isLeastFortunateOffset_five : IsLeastFortunateOffset 5 23 := by
  constructor
  · simpa [IsFortunateOffset, nthPrimorial_five] using
      (by norm_num : 1 < 23 ∧ Nat.Prime (2310 + 23))
  · intro k hk1 hk2
    have hkLow : 2 ≤ k := Nat.succ_le_of_lt hk1
    have hkHigh : k ≤ 22 := Nat.le_pred_of_lt hk2
    interval_cases k
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 2))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 3))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 4))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 5))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 6))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 7))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 8))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 9))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 10))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 11))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 12))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 13))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 14))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 15))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 16))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 17))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 18))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 19))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 20))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 21))
    · simpa [nthPrimorial_five] using (by norm_num : ¬Nat.Prime (2310 + 22))

theorem hasPrimeLeastFortunateOffset_five :
    ∃ m : Nat, IsLeastFortunateOffset 5 m ∧ Nat.Prime m := by
  exact ⟨23, isLeastFortunateOffset_five, by norm_num⟩

theorem hasPrimeLeastFortunateOffset_one_to_five {n : Nat}
    (hn1 : 1 ≤ n) (hn5 : n ≤ 5) :
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  interval_cases n
  · exact hasPrimeLeastFortunateOffset_one
  · exact hasPrimeLeastFortunateOffset_two
  · exact hasPrimeLeastFortunateOffset_three
  · exact hasPrimeLeastFortunateOffset_four
  · exact hasPrimeLeastFortunateOffset_five

end Fortune
