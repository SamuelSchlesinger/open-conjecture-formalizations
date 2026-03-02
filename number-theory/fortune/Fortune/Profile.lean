import Fortune.Bridge

namespace Fortune

/-- Any prime divisor of a Fortunate offset lies above `lastIncludedPrime n`. -/
theorem prime_divisor_gt_lastIncludedPrime_of_fortunateOffset {n m p : Nat}
    (hn : 1 ≤ n)
    (hOffset : IsFortunateOffset n m)
    (hp : Nat.Prime p)
    (hpdvd : p ∣ m) :
    lastIncludedPrime n < p := by
  refine lt_of_not_ge ?_
  intro hp_le_last
  obtain ⟨k, -, hk⟩ := Nat.exists_lt_card_nth_eq (p := Nat.Prime) hp
  have hk' : nthPrime k = p := by simpa [nthPrime] using hk
  have hkPrime_le_last : nthPrime k ≤ lastIncludedPrime n := by
    simpa [hk'] using hp_le_last
  have hk_le_pred : k ≤ n - 1 := by
    exact
      (Nat.nth_le_nth Nat.infinite_setOf_prime).1
        (by simpa [nthPrime] using hkPrime_le_last)
  have hpred_lt_n : n - 1 < n := Nat.sub_lt (Nat.succ_le_iff.mp hn) (by decide : 0 < 1)
  have hk_lt_n : k < n := lt_of_le_of_lt hk_le_pred hpred_lt_n
  have hnot_div : ¬nthPrime k ∣ m := fortunateOffset_not_dvd_nthPrime hOffset hk_lt_n
  have hk_dvd_m : nthPrime k ∣ m := by simpa [hk'] using hpdvd
  exact hnot_div hk_dvd_m

/-- Prime-divisor profile for least Fortunate offsets: every prime divisor of `m`
is strictly larger than the last included prime. -/
theorem prime_divisor_gt_lastIncludedPrime_of_leastOffset {n m p : Nat}
    (hn : 1 ≤ n)
    (hLeast : IsLeastFortunateOffset n m)
    (hp : Nat.Prime p)
    (hpdvd : p ∣ m) :
    lastIncludedPrime n < p :=
  prime_divisor_gt_lastIncludedPrime_of_fortunateOffset hn hLeast.1 hp hpdvd

/-- Any nontrivial divisor of a Fortunate offset lies above `lastIncludedPrime n`. -/
theorem divisor_gt_lastIncludedPrime_of_fortunateOffset {n m d : Nat}
    (hn : 1 ≤ n)
    (hOffset : IsFortunateOffset n m)
    (hd_gt_one : 1 < d)
    (hddvd : d ∣ m) :
    lastIncludedPrime n < d := by
  let p := Nat.minFac d
  have hp_prime : Nat.Prime p := Nat.minFac_prime (n := d) (ne_of_gt hd_gt_one)
  have hp_dvd_d : p ∣ d := Nat.minFac_dvd d
  have hp_dvd_m : p ∣ m := dvd_trans hp_dvd_d hddvd
  have hlast_lt_p : lastIncludedPrime n < p :=
    prime_divisor_gt_lastIncludedPrime_of_fortunateOffset hn hOffset hp_prime hp_dvd_m
  have hd_pos : 0 < d := lt_trans (by decide : 0 < 1) hd_gt_one
  have hp_le_d : p ≤ d := Nat.minFac_le hd_pos
  exact lt_of_lt_of_le hlast_lt_p hp_le_d

/-- Any nontrivial divisor of a least Fortunate offset lies above `lastIncludedPrime n`. -/
theorem divisor_gt_lastIncludedPrime_of_leastOffset {n m d : Nat}
    (hn : 1 ≤ n)
    (hLeast : IsLeastFortunateOffset n m)
    (hd_gt_one : 1 < d)
    (hddvd : d ∣ m) :
    lastIncludedPrime n < d :=
  divisor_gt_lastIncludedPrime_of_fortunateOffset hn hLeast.1 hd_gt_one hddvd

/-- Least Fortunate offsets are coprime to `primorial (lastIncludedPrime n)`. -/
theorem leastOffset_coprime_primorial_lastIncludedPrime {n m : Nat}
    (hn : 1 ≤ n) (hLeast : IsLeastFortunateOffset n m) :
    Nat.Coprime m (primorial (lastIncludedPrime n)) := by
  have hcop : Nat.Coprime m (nthPrimorial n) := fortunateOffset_coprime_nthPrimorial hLeast.1
  have hprimorial : nthPrimorial n = primorial (lastIncludedPrime n) :=
    bridge_nthPrimorial_eq_primorial_lastIncludedPrime n hn
  simpa [hprimorial] using hcop

/-- No nontrivial divisor at most `lastIncludedPrime n` can divide a least offset. -/
theorem leastOffset_not_dvd_of_le_lastIncludedPrime {n m d : Nat}
    (hn : 1 ≤ n)
    (hLeast : IsLeastFortunateOffset n m)
    (hd_gt_one : 1 < d)
    (hd_le : d ≤ lastIncludedPrime n) :
    ¬ d ∣ m := by
  intro hddvd
  have hlast_lt_d : lastIncludedPrime n < d :=
    divisor_gt_lastIncludedPrime_of_leastOffset hn hLeast hd_gt_one hddvd
  exact (Nat.not_lt_of_ge hd_le) hlast_lt_d

/-- Equivalent threshold-primorial coprimality profile for indexed Fortunate offsets. -/
theorem fortunateOffset_coprime_primorial_lastIncludedPrime {n m : Nat}
    (hn : 1 ≤ n) (hOffset : IsFortunateOffset n m) :
    Nat.Coprime m (primorial (lastIncludedPrime n)) := by
  have hcop : Nat.Coprime m (nthPrimorial n) := fortunateOffset_coprime_nthPrimorial hOffset
  have hprimorial : nthPrimorial n = primorial (lastIncludedPrime n) :=
    bridge_nthPrimorial_eq_primorial_lastIncludedPrime n hn
  simpa [hprimorial] using hcop

end Fortune
