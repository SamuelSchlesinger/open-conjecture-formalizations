import Fortune.Structure

namespace Fortune

theorem minFac_gt_lastIncludedPrime_of_fortunateOffset {n m : Nat}
    (hn : 1 ≤ n) (hOffset : IsFortunateOffset n m) :
    lastIncludedPrime n < Nat.minFac m := by
  refine lt_of_not_ge ?_
  intro hmin_le_last
  have hm_ne_one : m ≠ 1 := ne_of_gt hOffset.1
  have hmin_prime : Nat.Prime (Nat.minFac m) := Nat.minFac_prime hm_ne_one
  obtain ⟨k, -, hk⟩ := Nat.exists_lt_card_nth_eq (p := Nat.Prime) hmin_prime
  have hk' : nthPrime k = Nat.minFac m := by simpa [nthPrime] using hk
  have hkPrime_le_last : nthPrime k ≤ lastIncludedPrime n := by
    simpa [lastIncludedPrime, hk'] using hmin_le_last
  have hk_le_pred : k ≤ n - 1 := by
    exact (Nat.nth_le_nth Nat.infinite_setOf_prime).1 (by simpa [nthPrime] using hkPrime_le_last)
  have hpred_lt_n : n - 1 < n := Nat.sub_lt (Nat.succ_le_iff.mp hn) (by decide : 0 < 1)
  have hk_lt_n : k < n := lt_of_le_of_lt hk_le_pred hpred_lt_n
  have hnot_div : ¬nthPrime k ∣ m := fortunateOffset_not_dvd_nthPrime hOffset hk_lt_n
  have hmin_dvd : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have hk_dvd_m : nthPrime k ∣ m := by simpa [hk'] using hmin_dvd
  exact hnot_div hk_dvd_m

theorem lastIncludedPrime_lt_offset_of_fortunateOffset {n m : Nat}
    (hn : 1 ≤ n) (hOffset : IsFortunateOffset n m) :
    lastIncludedPrime n < m := by
  have hmin_lt : lastIncludedPrime n < Nat.minFac m :=
    minFac_gt_lastIncludedPrime_of_fortunateOffset hn hOffset
  have hm_pos : 0 < m := lt_trans (by decide : 0 < 1) hOffset.1
  have hmin_le_m : Nat.minFac m ≤ m := Nat.minFac_le hm_pos
  exact lt_of_lt_of_le hmin_lt hmin_le_m

theorem succ_lastIncludedPrime_sq_le_offset_of_composite_fortunateOffset {n m : Nat}
    (hn : 1 ≤ n) (hOffset : IsFortunateOffset n m) (hComp : ¬Nat.Prime m) :
    (lastIncludedPrime n + 1) ^ 2 ≤ m := by
  have hmin_gt : lastIncludedPrime n < Nat.minFac m :=
    minFac_gt_lastIncludedPrime_of_fortunateOffset hn hOffset
  have hsucc_le_min : lastIncludedPrime n + 1 ≤ Nat.minFac m := Nat.succ_le_of_lt hmin_gt
  have hsq_le_minsq : (lastIncludedPrime n + 1) ^ 2 ≤ Nat.minFac m ^ 2 :=
    Nat.pow_le_pow_left hsucc_le_min 2
  have hm_pos : 0 < m := lt_trans (by decide : 0 < 1) hOffset.1
  have hminsq_le_m : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self hm_pos hComp
  exact hsq_le_minsq.trans hminsq_le_m

end Fortune
