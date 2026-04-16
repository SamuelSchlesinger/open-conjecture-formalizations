import Fortune.IntervalExistence
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.LucasPrimality

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

/-- Explicit value for the seventh indexed prime. -/
theorem nthPrime_six_eq_seventeen : nthPrime 6 = 17 := by
  have h17prime : Nat.Prime 17 := by decide
  have hcount : Nat.count Nat.Prime 17 = 6 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 17) = 17 := Nat.nth_count h17prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_seven_eq_seventeen : lastIncludedPrime 7 = 17 := by
  simpa [lastIncludedPrime] using nthPrime_six_eq_seventeen

/-- Explicit value for the eighth indexed prime. -/
theorem nthPrime_seven_eq_nineteen : nthPrime 7 = 19 := by
  have h19prime : Nat.Prime 19 := by decide
  have hcount : Nat.count Nat.Prime 19 = 7 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 19) = 19 := Nat.nth_count h19prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_eight_eq_nineteen : lastIncludedPrime 8 = 19 := by
  simpa [lastIncludedPrime] using nthPrime_seven_eq_nineteen

/-- Explicit value for the ninth indexed prime. -/
theorem nthPrime_eight_eq_twenty_three : nthPrime 8 = 23 := by
  have h23prime : Nat.Prime 23 := by decide
  have hcount : Nat.count Nat.Prime 23 = 8 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 23) = 23 := Nat.nth_count h23prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_nine_eq_twenty_three : lastIncludedPrime 9 = 23 := by
  simpa [lastIncludedPrime] using nthPrime_eight_eq_twenty_three

/-- Explicit value for the tenth indexed prime. -/
theorem nthPrime_nine_eq_twenty_nine : nthPrime 9 = 29 := by
  have h29prime : Nat.Prime 29 := by decide
  have hcount : Nat.count Nat.Prime 29 = 9 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 29) = 29 := Nat.nth_count h29prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_ten_eq_twenty_nine : lastIncludedPrime 10 = 29 := by
  simpa [lastIncludedPrime] using nthPrime_nine_eq_twenty_nine

/-- Explicit value for the eleventh indexed prime. -/
theorem nthPrime_ten_eq_thirty_one : nthPrime 10 = 31 := by
  have h31prime : Nat.Prime 31 := by decide
  have hcount : Nat.count Nat.Prime 31 = 10 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 31) = 31 := Nat.nth_count h31prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_eleven_eq_thirty_one : lastIncludedPrime 11 = 31 := by
  simpa [lastIncludedPrime] using nthPrime_ten_eq_thirty_one

/-- Explicit value for the twelfth indexed prime. -/
theorem nthPrime_eleven_eq_thirty_seven : nthPrime 11 = 37 := by
  have h37prime : Nat.Prime 37 := by decide
  have hcount : Nat.count Nat.Prime 37 = 11 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 37) = 37 := Nat.nth_count h37prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_twelve_eq_thirty_seven : lastIncludedPrime 12 = 37 := by
  simpa [lastIncludedPrime] using nthPrime_eleven_eq_thirty_seven

/-- Explicit value for the thirteenth indexed prime. -/
theorem nthPrime_twelve_eq_forty_one : nthPrime 12 = 41 := by
  have h41prime : Nat.Prime 41 := by decide
  have hcount : Nat.count Nat.Prime 41 = 12 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 41) = 41 := Nat.nth_count h41prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_thirteen_eq_forty_one : lastIncludedPrime 13 = 41 := by
  simpa [lastIncludedPrime] using nthPrime_twelve_eq_forty_one

/-- Explicit value for the fourteenth indexed prime. -/
theorem nthPrime_thirteen_eq_forty_three : nthPrime 13 = 43 := by
  have h43prime : Nat.Prime 43 := by decide
  have hcount : Nat.count Nat.Prime 43 = 13 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 43) = 43 := Nat.nth_count h43prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_fourteen_eq_forty_three : lastIncludedPrime 14 = 43 := by
  simpa [lastIncludedPrime] using nthPrime_thirteen_eq_forty_three

/-- Explicit value for the fifteenth indexed prime. -/
theorem nthPrime_fourteen_eq_forty_seven : nthPrime 14 = 47 := by
  have h47prime : Nat.Prime 47 := by decide
  have hcount : Nat.count Nat.Prime 47 = 14 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 47) = 47 := Nat.nth_count h47prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_fifteen_eq_forty_seven : lastIncludedPrime 15 = 47 := by
  simpa [lastIncludedPrime] using nthPrime_fourteen_eq_forty_seven

/-- Explicit value for the sixteenth indexed prime. -/
theorem nthPrime_fifteen_eq_fifty_three : nthPrime 15 = 53 := by
  have h53prime : Nat.Prime 53 := by decide
  have hcount : Nat.count Nat.Prime 53 = 15 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 53) = 53 := Nat.nth_count h53prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_sixteen_eq_fifty_three : lastIncludedPrime 16 = 53 := by
  simpa [lastIncludedPrime] using nthPrime_fifteen_eq_fifty_three

/-- Explicit value for the seventeenth indexed prime. -/
theorem nthPrime_sixteen_eq_fifty_nine : nthPrime 16 = 59 := by
  have h59prime : Nat.Prime 59 := by decide
  have hcount : Nat.count Nat.Prime 59 = 16 := by native_decide
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 59) = 59 := Nat.nth_count h59prime
  simpa [nthPrime, hcount] using hnth

theorem lastIncludedPrime_seventeen_eq_fifty_nine : lastIncludedPrime 17 = 59 := by
  simpa [lastIncludedPrime] using nthPrime_sixteen_eq_fifty_nine

private theorem prime_4211 : Nat.Prime 4211 := by
  native_decide

private theorem prime_10789 : Nat.Prime 10789 := by
  native_decide

private theorem prime_dvd_84220_cases {q : Nat}
    (hq : Nat.Prime q) (hqd : q ∣ 84221 - 1) :
    q = 2 ∨ q = 5 ∨ q = 4211 := by
  have hqd' : q ∣ 2 * (2 * (5 * 4211)) := by
    norm_num at hqd ⊢
    exact hqd
  rcases hq.dvd_mul.mp hqd' with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq5 | hq4211
  · exact Or.inr <| Or.inl (((Nat.dvd_prime Nat.prime_five).1 hq5).resolve_left hq.ne_one)
  · exact Or.inr <| Or.inr (((Nat.dvd_prime prime_4211).1 hq4211).resolve_left hq.ne_one)

private theorem prime_84221 : Nat.Prime 84221 := by
  refine lucas_primality 84221 (2 : ZMod 84221) ?_ ?_
  · native_decide
  · intro q hq hqd
    rcases prime_dvd_84220_cases hq hqd with rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide

private theorem prime_dvd_6371318650_cases {q : Nat}
    (hq : Nat.Prime q) (hqd : q ∣ 6371318651 - 1) :
    q = 2 ∨ q = 5 ∨ q = 17 ∨ q = 89 ∨ q = 84221 := by
  have hqd' : q ∣ 2 * (5 * (5 * (17 * (89 * 84221)))) := by
    norm_num at hqd ⊢
    exact hqd
  rcases hq.dvd_mul.mp hqd' with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq5 | hrest
  · exact Or.inr <| Or.inl (((Nat.dvd_prime Nat.prime_five).1 hq5).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq5 | hrest
  · exact Or.inr <| Or.inl (((Nat.dvd_prime Nat.prime_five).1 hq5).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq17 | hrest
  · exact Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 17)).1 hq17).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq89 | hq84221
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 89)).1 hq89).resolve_left hq.ne_one)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (((Nat.dvd_prime prime_84221).1 hq84221).resolve_left hq.ne_one)

private theorem prime_6371318651 : Nat.Prime 6371318651 := by
  refine lucas_primality 6371318651 (2 : ZMod 6371318651) ?_ ?_
  · native_decide
  · intro q hq hqd
    rcases prime_dvd_6371318650_cases hq hqd with rfl | rfl | rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide

private theorem prime_dvd_32589158477190044788_cases {q : Nat}
    (hq : Nat.Prime q) (hqd : q ∣ 32589158477190044789 - 1) :
    q = 2 ∨ q = 29 ∨ q = 61 ∨ q = 67 ∨ q = 10789 ∨ q = 6371318651 := by
  have hqd' : q ∣ 2 * (2 * (29 * (61 * (67 * (10789 * 6371318651))))) := by
    norm_num at hqd ⊢
    exact hqd
  rcases hq.dvd_mul.mp hqd' with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq29 | hrest
  · exact Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 29)).1 hq29).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq61 | hrest
  · exact Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 61)).1 hq61).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq67 | hrest
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 67)).1 hq67).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq10789 | hqBig
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime prime_10789).1 hq10789).resolve_left hq.ne_one)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (((Nat.dvd_prime prime_6371318651).1 hqBig).resolve_left hq.ne_one)

private theorem prime_32589158477190044789 : Nat.Prime 32589158477190044789 := by
  refine lucas_primality 32589158477190044789 (2 : ZMod 32589158477190044789) ?_ ?_
  · native_decide
  · intro q hq hqd
    rcases prime_dvd_32589158477190044788_cases hq hqd with rfl | rfl | rfl | rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide

private theorem prime_342131 : Nat.Prime 342131 := by
  native_decide

private theorem prime_946411 : Nat.Prime 946411 := by
  native_decide

private theorem prime_dvd_1265200438_cases {q : Nat}
    (hq : Nat.Prime q) (hqd : q ∣ 1265200439 - 1) :
    q = 2 ∨ q = 43 ∨ q = 342131 := by
  have hqd' : q ∣ 2 * (43 * (43 * 342131)) := by
    norm_num at hqd ⊢
    exact hqd
  rcases hq.dvd_mul.mp hqd' with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq43 | hrest
  · exact Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 43)).1 hq43).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq43 | hq342131
  · exact Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 43)).1 hq43).resolve_left hq.ne_one)
  · exact Or.inr <| Or.inr (((Nat.dvd_prime prime_342131).1 hq342131).resolve_left hq.ne_one)

private theorem prime_1265200439 : Nat.Prime 1265200439 := by
  refine lucas_primality 1265200439 (29 : ZMod 1265200439) ?_ ?_
  · native_decide
  · intro q hq hqd
    rcases prime_dvd_1265200438_cases hq hqd with rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide

private theorem prime_dvd_16885865062_cases {q : Nat}
    (hq : Nat.Prime q) (hqd : q ∣ 16885865063 - 1) :
    q = 2 ∨ q = 11 ∨ q = 811 ∨ q = 946411 := by
  have hqd' : q ∣ 2 * (11 * (811 * 946411)) := by
    norm_num at hqd ⊢
    exact hqd
  rcases hq.dvd_mul.mp hqd' with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq11 | hrest
  · exact Or.inr <| Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 11)).1 hq11).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq811 | hq946411
  · exact Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime (by native_decide : Nat.Prime 811)).1 hq811).resolve_left hq.ne_one)
  · exact Or.inr <| Or.inr <| Or.inr (((Nat.dvd_prime prime_946411).1 hq946411).resolve_left hq.ne_one)

private theorem prime_16885865063 : Nat.Prime 16885865063 := by
  refine lucas_primality 16885865063 (5 : ZMod 16885865063) ?_ ?_
  · native_decide
  · intro q hq hqd
    rcases prime_dvd_16885865062_cases hq hqd with rfl | rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide
    · native_decide

private theorem prime_dvd_1922760350154212639130_cases {q : Nat}
    (hq : Nat.Prime q) (hqd : q ∣ 1922760350154212639131 - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 1265200439 ∨ q = 16885865063 := by
  have hqd' : q ∣ 2 * (3 * (3 * (5 * (1265200439 * 16885865063)))) := by
    norm_num at hqd ⊢
    exact hqd
  rcases hq.dvd_mul.mp hqd' with hq2 | hrest
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).1 hq2).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq3 | hrest
  · exact Or.inr <| Or.inl (((Nat.dvd_prime Nat.prime_three).1 hq3).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq3 | hrest
  · exact Or.inr <| Or.inl (((Nat.dvd_prime Nat.prime_three).1 hq3).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hq5 | hrest
  · exact Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime Nat.prime_five).1 hq5).resolve_left hq.ne_one)
  rcases hq.dvd_mul.mp hrest with hqLeft | hqRight
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (((Nat.dvd_prime prime_1265200439).1 hqLeft).resolve_left hq.ne_one)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (((Nat.dvd_prime prime_16885865063).1 hqRight).resolve_left hq.ne_one)

private theorem prime_1922760350154212639131 : Nat.Prime 1922760350154212639131 := by
  refine lucas_primality 1922760350154212639131 (2 : ZMod 1922760350154212639131) ?_ ?_
  · native_decide
  · intro q hq hqd
    rcases prime_dvd_1922760350154212639130_cases hq hqd with rfl | rfl | rfl | rfl | rfl
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · native_decide

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

/-- Finite verified interval-prime existence for Route 2 at `1 ≤ n ≤ 12`. -/
theorem route2_intervalPrimeExistence_one_to_twelve {n r : Nat}
    (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r := by
  interval_cases n
  · exact route2_intervalPrimeExistence_one_to_six (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_six (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_six (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_six (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_six (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_six (by decide) (by decide) hqr
  · have hq_lt_r : 17 < r := by
      simpa [lastIncludedPrime_seven_eq_seventeen] using hqr.2.2.1
    have hm_lt_sq : 19 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 19 < (17 + 1) ^ 2)
    simpa [lastIncludedPrime_seven_eq_seventeen] using
      (intervalPrimeExistsAtPrime_of_offset (q := 17) (r := r) (m := 19)
        (by decide : 1 < 19) hm_lt_sq (by native_decide : Nat.Prime (primorial 17 + 19)))
  · have hq_lt_r : 19 < r := by
      simpa [lastIncludedPrime_eight_eq_nineteen] using hqr.2.2.1
    have hm_lt_sq : 23 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 23 < (19 + 1) ^ 2)
    simpa [lastIncludedPrime_eight_eq_nineteen] using
      (intervalPrimeExistsAtPrime_of_offset (q := 19) (r := r) (m := 23)
        (by decide : 1 < 23) hm_lt_sq (by native_decide : Nat.Prime (primorial 19 + 23)))
  · have hq_lt_r : 23 < r := by
      simpa [lastIncludedPrime_nine_eq_twenty_three] using hqr.2.2.1
    have hm_lt_sq : 37 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 37 < (23 + 1) ^ 2)
    simpa [lastIncludedPrime_nine_eq_twenty_three] using
      (intervalPrimeExistsAtPrime_of_offset (q := 23) (r := r) (m := 37)
        (by decide : 1 < 37) hm_lt_sq (by native_decide : Nat.Prime (primorial 23 + 37)))
  · have hq_lt_r : 29 < r := by
      simpa [lastIncludedPrime_ten_eq_twenty_nine] using hqr.2.2.1
    have hm_lt_sq : 61 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 61 < (29 + 1) ^ 2)
    simpa [lastIncludedPrime_ten_eq_twenty_nine] using
      (intervalPrimeExistsAtPrime_of_offset (q := 29) (r := r) (m := 61)
        (by decide : 1 < 61) hm_lt_sq (by native_decide : Nat.Prime (primorial 29 + 61)))
  · have hq_lt_r : 31 < r := by
      simpa [lastIncludedPrime_eleven_eq_thirty_one] using hqr.2.2.1
    have hm_lt_sq : 67 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 67 < (31 + 1) ^ 2)
    simpa [lastIncludedPrime_eleven_eq_thirty_one] using
      (intervalPrimeExistsAtPrime_of_offset (q := 31) (r := r) (m := 67)
        (by decide : 1 < 67) hm_lt_sq (by native_decide : Nat.Prime (primorial 31 + 67)))
  · have hq_lt_r : 37 < r := by
      simpa [lastIncludedPrime_twelve_eq_thirty_seven] using hqr.2.2.1
    have hm_lt_sq : 61 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 61 < (37 + 1) ^ 2)
    simpa [lastIncludedPrime_twelve_eq_thirty_seven] using
      (intervalPrimeExistsAtPrime_of_offset (q := 37) (r := r) (m := 61)
        (by decide : 1 < 61) hm_lt_sq (by native_decide : Nat.Prime (primorial 37 + 61)))

/-- Finite verified Route 2.A bound for `1 ≤ n ≤ 12`. -/
theorem route2_reductionBound_one_to_twelve {n m r : Nat}
    (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hLeast : IsLeastFortunateOffset n m)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    m < r ^ 2 := by
  have hInt : IntervalPrimeExistsAtPrime (lastIncludedPrime n) r :=
    route2_intervalPrimeExistence_one_to_twelve hn1 hn12 hqr
  rcases hInt with ⟨p, hp, hlow, hhigh⟩
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn1).1 hLeast
  exact leastOffsetAtPrime_lt_nextPrime_sq_of_intervalPrime hqr hLeastAtPrime hp hlow hhigh

/-- Finite verified interval-prime existence for Route 2 at `1 ≤ n ≤ 15`. -/
theorem route2_intervalPrimeExistence_one_to_fifteen {n r : Nat}
    (hn1 : 1 ≤ n) (hn15 : n ≤ 15)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r := by
  interval_cases n
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_twelve (by decide) (by decide) hqr
  · have hq_lt_r : 41 < r := by
      simpa [lastIncludedPrime_thirteen_eq_forty_one] using hqr.2.2.1
    have hm_lt_sq : 71 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 71 < (41 + 1) ^ 2)
    simpa [lastIncludedPrime_thirteen_eq_forty_one] using
      (intervalPrimeExistsAtPrime_of_offset (q := 41) (r := r) (m := 71)
        (by decide : 1 < 71) hm_lt_sq (by native_decide : Nat.Prime (primorial 41 + 71)))
  · have hq_lt_r : 43 < r := by
      simpa [lastIncludedPrime_fourteen_eq_forty_three] using hqr.2.2.1
    have hm_lt_sq : 47 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 47 < (43 + 1) ^ 2)
    simpa [lastIncludedPrime_fourteen_eq_forty_three] using
      (intervalPrimeExistsAtPrime_of_offset (q := 43) (r := r) (m := 47)
        (by decide : 1 < 47) hm_lt_sq (by native_decide : Nat.Prime (primorial 43 + 47)))
  · have hq_lt_r : 47 < r := by
      simpa [lastIncludedPrime_fifteen_eq_forty_seven] using hqr.2.2.1
    have hm_lt_sq : 107 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 107 < (47 + 1) ^ 2)
    simpa [lastIncludedPrime_fifteen_eq_forty_seven] using
      (intervalPrimeExistsAtPrime_of_offset (q := 47) (r := r) (m := 107)
        (by decide : 1 < 107) hm_lt_sq (by native_decide : Nat.Prime (primorial 47 + 107)))

/-- Finite verified Route 2.A bound for `1 ≤ n ≤ 15`. -/
theorem route2_reductionBound_one_to_fifteen {n m r : Nat}
    (hn1 : 1 ≤ n) (hn15 : n ≤ 15)
    (hLeast : IsLeastFortunateOffset n m)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    m < r ^ 2 := by
  have hInt : IntervalPrimeExistsAtPrime (lastIncludedPrime n) r :=
    route2_intervalPrimeExistence_one_to_fifteen hn1 hn15 hqr
  rcases hInt with ⟨p, hp, hlow, hhigh⟩
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn1).1 hLeast
  exact leastOffsetAtPrime_lt_nextPrime_sq_of_intervalPrime hqr hLeastAtPrime hp hlow hhigh

/-- Finite verified interval-prime existence for Route 2 at `1 ≤ n ≤ 16`. -/
theorem route2_intervalPrimeExistence_one_to_sixteen {n r : Nat}
    (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r := by
  interval_cases n
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_fifteen (by decide) (by decide) hqr
  · have hq_lt_r : 53 < r := by
      simpa [lastIncludedPrime_sixteen_eq_fifty_three] using hqr.2.2.1
    have hm_lt_sq : 59 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 59 < (53 + 1) ^ 2)
    simpa [lastIncludedPrime_sixteen_eq_fifty_three] using
      (intervalPrimeExistsAtPrime_of_offset (q := 53) (r := r) (m := 59)
        (by decide : 1 < 59) hm_lt_sq prime_32589158477190044789)

/-- Finite verified Route 2.A bound for `1 ≤ n ≤ 16`. -/
theorem route2_reductionBound_one_to_sixteen {n m r : Nat}
    (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (hLeast : IsLeastFortunateOffset n m)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    m < r ^ 2 := by
  have hInt : IntervalPrimeExistsAtPrime (lastIncludedPrime n) r :=
    route2_intervalPrimeExistence_one_to_sixteen hn1 hn16 hqr
  rcases hInt with ⟨p, hp, hlow, hhigh⟩
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn1).1 hLeast
  exact leastOffsetAtPrime_lt_nextPrime_sq_of_intervalPrime hqr hLeastAtPrime hp hlow hhigh

/-- Finite verified interval-prime existence for Route 2 at `1 ≤ n ≤ 17`. -/
theorem route2_intervalPrimeExistence_one_to_seventeen {n r : Nat}
    (hn1 : 1 ≤ n) (hn17 : n ≤ 17)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r := by
  interval_cases n
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · exact route2_intervalPrimeExistence_one_to_sixteen (by decide) (by decide) hqr
  · have hq_lt_r : 59 < r := by
      simpa [lastIncludedPrime_seventeen_eq_fifty_nine] using hqr.2.2.1
    have hm_lt_sq : 61 < r ^ 2 :=
      lt_sq_of_lt_with_constant hq_lt_r (by decide : 61 < (59 + 1) ^ 2)
    simpa [lastIncludedPrime_seventeen_eq_fifty_nine] using
      (intervalPrimeExistsAtPrime_of_offset (q := 59) (r := r) (m := 61)
        (by decide : 1 < 61) hm_lt_sq prime_1922760350154212639131)

/-- Finite verified Route 2.A bound for `1 ≤ n ≤ 17`. -/
theorem route2_reductionBound_one_to_seventeen {n m r : Nat}
    (hn1 : 1 ≤ n) (hn17 : n ≤ 17)
    (hLeast : IsLeastFortunateOffset n m)
    (hqr : ConsecutivePrimes (lastIncludedPrime n) r) :
    m < r ^ 2 := by
  have hInt : IntervalPrimeExistsAtPrime (lastIncludedPrime n) r :=
    route2_intervalPrimeExistence_one_to_seventeen hn1 hn17 hqr
  rcases hInt with ⟨p, hp, hlow, hhigh⟩
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn1).1 hLeast
  exact leastOffsetAtPrime_lt_nextPrime_sq_of_intervalPrime hqr hLeastAtPrime hp hlow hhigh

end Fortune
