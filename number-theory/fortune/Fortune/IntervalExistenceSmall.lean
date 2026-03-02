import Fortune.IntervalExistence
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.PrimeCounting

namespace Fortune

private theorem intervalPrimeExistsAtPrime_of_offset {q r m : Nat}
    (hm_gt_one : 1 < m)
    (hm_lt_sq : m < r ^ 2)
    (hprime : Nat.Prime (primorial q + m)) :
    IntervalPrimeExistsAtPrime q r :=
  ⟨primorial q + m, hprime, Nat.add_lt_add_left hm_gt_one (primorial q),
    Nat.add_lt_add_left hm_lt_sq (primorial q)⟩

private theorem lt_sq_of_lt_with_constant {a r m : Nat}
    (ha_lt_r : a < r)
    (hm_lt_const : m < (a + 1) ^ 2) :
    m < r ^ 2 := by
  have hasucc_le_r : a + 1 ≤ r := Nat.succ_le_of_lt ha_lt_r
  have hsq_le : (a + 1) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hasucc_le_r 2
  exact lt_of_lt_of_le hm_lt_const hsq_le

/-- Explicit value for the sixth indexed prime. -/
theorem nthPrime_five_eq_thirteen : nthPrime 5 = 13 := by
  have h13prime : Nat.Prime 13 := by decide
  have hcount : Nat.count Nat.Prime 13 = 5 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 13) = 13 := Nat.nth_count h13prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_six_eq_thirteen : lastIncludedPrime 6 = 13 := by
  simpa [lastIncludedPrime] using nthPrime_five_eq_thirteen

/-- Finite verified interval-prime existence for Route 2 at `1 ≤ n ≤ 6`. -/
theorem route2_intervalPrimeExistence_one_to_six {n r : Nat}
    (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r := by
  interval_cases n
  · have hq_lt_r : 2 < r := by
      simpa [lastIncludedPrime, nthPrime] using hqr.2.2.1
    have hm_lt_sq : 3 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 3 < (2 + 1) ^ 2)
    simpa [lastIncludedPrime, nthPrime] using
      (intervalPrimeExistsAtPrime_of_offset (q := 2) (r := r) (m := 3)
        (by decide : 1 < 3) hm_lt_sq (by native_decide : Nat.Prime (primorial 2 + 3)))
  · have hq_lt_r : 3 < r := by
      simpa [lastIncludedPrime, nthPrime] using hqr.2.2.1
    have hm_lt_sq : 5 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 5 < (3 + 1) ^ 2)
    simpa [lastIncludedPrime, nthPrime] using
      (intervalPrimeExistsAtPrime_of_offset (q := 3) (r := r) (m := 5)
        (by decide : 1 < 5) hm_lt_sq (by native_decide : Nat.Prime (primorial 3 + 5)))
  · have hq_lt_r : 5 < r := by
      simpa [lastIncludedPrime, nthPrime] using hqr.2.2.1
    have hm_lt_sq : 7 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 7 < (5 + 1) ^ 2)
    simpa [lastIncludedPrime, nthPrime] using
      (intervalPrimeExistsAtPrime_of_offset (q := 5) (r := r) (m := 7)
        (by decide : 1 < 7) hm_lt_sq (by native_decide : Nat.Prime (primorial 5 + 7)))
  · have hq_lt_r : 7 < r := by
      simpa [lastIncludedPrime, nthPrime] using hqr.2.2.1
    have hm_lt_sq : 13 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 13 < (7 + 1) ^ 2)
    simpa [lastIncludedPrime, nthPrime] using
      (intervalPrimeExistsAtPrime_of_offset (q := 7) (r := r) (m := 13)
        (by decide : 1 < 13) hm_lt_sq (by native_decide : Nat.Prime (primorial 7 + 13)))
  · have hq_lt_r : 11 < r := by
      simpa [lastIncludedPrime, nthPrime] using hqr.2.2.1
    have hm_lt_sq : 23 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 23 < (11 + 1) ^ 2)
    simpa [lastIncludedPrime, nthPrime] using
      (intervalPrimeExistsAtPrime_of_offset (q := 11) (r := r) (m := 23)
        (by decide : 1 < 23) hm_lt_sq (by native_decide : Nat.Prime (primorial 11 + 23)))
  · have hq_lt_r : 13 < r := by
      simpa [lastIncludedPrime_six_eq_thirteen] using hqr.2.2.1
    have hm_lt_sq : 17 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 17 < (13 + 1) ^ 2)
    simpa [lastIncludedPrime_six_eq_thirteen] using
      (intervalPrimeExistsAtPrime_of_offset (q := 13) (r := r) (m := 17)
        (by decide : 1 < 17) hm_lt_sq (by native_decide : Nat.Prime (primorial 13 + 17)))

/-- Finite verified interval-prime existence for Route 2 at `1 ≤ n ≤ 5`. -/
theorem route2_intervalPrimeExistence_one_to_five {n r : Nat}
    (hn1 : 1 ≤ n) (hn5 : n ≤ 5)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r := by
  exact route2_intervalPrimeExistence_one_to_six hn1 (le_trans hn5 (by decide : 5 ≤ 6)) hqr

/-- Finite verified Route 2.A bound for `1 ≤ n ≤ 6`. -/
theorem route2_reductionBound_one_to_six {n m r : Nat}
    (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
    (hLeast : IsLeastFortunateOffset n m)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    m < r ^ 2 := by
  have hInt : IntervalPrimeExistsAtPrime (lastIncludedPrime n) r :=
    route2_intervalPrimeExistence_one_to_six hn1 hn6 hqr
  rcases hInt with ⟨p, hp, hlow, hhigh⟩
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn1).1 hLeast
  exact leastOffsetAtPrime_lt_nextPrime_sq_of_intervalPrime hqr hLeastAtPrime hp hlow hhigh

/-- Finite verified Route 2.A bound for `1 ≤ n ≤ 5`. -/
theorem route2_reductionBound_one_to_five {n m r : Nat}
    (hn1 : 1 ≤ n) (hn5 : n ≤ 5)
    (hLeast : IsLeastFortunateOffset n m)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    m < r ^ 2 := by
  exact route2_reductionBound_one_to_six hn1 (le_trans hn5 (by decide : 5 ≤ 6)) hLeast hqr

end Fortune
