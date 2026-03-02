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

/-- Equivalent threshold-primorial coprimality profile for indexed Fortunate offsets. -/
theorem fortunateOffset_coprime_primorial_lastIncludedPrime {n m : Nat}
    (hn : 1 ≤ n) (hOffset : IsFortunateOffset n m) :
    Nat.Coprime m (primorial (lastIncludedPrime n)) := by
  have hcop : Nat.Coprime m (nthPrimorial n) := fortunateOffset_coprime_nthPrimorial hOffset
  have hprimorial : nthPrimorial n = primorial (lastIncludedPrime n) :=
    bridge_nthPrimorial_eq_primorial_lastIncludedPrime n hn
  simpa [hprimorial] using hcop

end Fortune
