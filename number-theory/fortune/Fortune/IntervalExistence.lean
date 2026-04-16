import Fortune.ReductionBound
import Fortune.Existence

namespace Fortune

/-- Prime-in-interval formulation at threshold `q`. -/
def IntervalPrimeExistsAtPrime (q r : Nat) : Prop :=
  ∃ p : Nat, Nat.Prime p ∧
    primorial q + 1 < p ∧
    p < primorial q + r ^ 2

/-- Offset-in-interval formulation at threshold `q`. -/
def OffsetPrimeExistsAtPrime (q r : Nat) : Prop :=
  ∃ k : Nat, 1 < k ∧
    k < r ^ 2 ∧
    Nat.Prime (primorial q + k)

/-- Stronger research-target formulation:
there exists a prime offset `m` strictly above `q` and below `r^2`
such that `q# + m` is prime. -/
def PrimeOffsetPrimeExistsAtPrime (q r : Nat) : Prop :=
  ∃ m : Nat, Nat.Prime m ∧
    q < m ∧
    m < r ^ 2 ∧
    Nat.Prime (primorial q + m)

/-- The two upper-interval existence formulations are equivalent. -/
theorem intervalPrimeExistsAtPrime_iff_offsetPrimeExistsAtPrime {q r : Nat} :
    IntervalPrimeExistsAtPrime q r ↔ OffsetPrimeExistsAtPrime q r := by
  constructor
  · intro h
    rcases h with ⟨p, hp, hlow, hhigh⟩
    have hprim_le_p : primorial q ≤ p := Nat.le_of_lt
      (lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < 1)) hlow)
    refine ⟨p - primorial q, ?_, ?_, ?_⟩
    · have htwo_le_sub : 2 ≤ p - primorial q := by
        have htwo_plus_prim_le_p : 2 + primorial q ≤ p := by
          have : primorial q + 2 ≤ p := Nat.succ_le_of_lt hlow
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
        exact Nat.le_sub_of_add_le htwo_plus_prim_le_p
      exact lt_of_lt_of_le (by decide : 1 < 2) htwo_le_sub
    · exact (Nat.sub_lt_iff_lt_add hprim_le_p).2 (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhigh)
    · have hsum : primorial q + (p - primorial q) = p := Nat.add_sub_of_le hprim_le_p
      simpa [hsum] using hp
  · intro h
    rcases h with ⟨k, hk_gt_one, hk_lt_sq, hk_prime_sum⟩
    refine ⟨primorial q + k, hk_prime_sum, ?_, ?_⟩
    · exact Nat.add_lt_add_left hk_gt_one (primorial q)
    · exact Nat.add_lt_add_left hk_lt_sq (primorial q)

/-- The prime-offset formulation is stronger than the plain offset formulation. -/
theorem offsetPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime {q r : Nat} :
    PrimeOffsetPrimeExistsAtPrime q r → OffsetPrimeExistsAtPrime q r := by
  intro h
  rcases h with ⟨m, hmPrime, _hq_lt_m, hm_lt_sq, hm_prime_sum⟩
  refine ⟨m, ?_, hm_lt_sq, hm_prime_sum⟩
  exact lt_of_lt_of_le (by decide : 1 < 2) hmPrime.two_le

/-- Hence the prime-offset formulation also implies the interval-prime formulation. -/
theorem intervalPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime {q r : Nat} :
    PrimeOffsetPrimeExistsAtPrime q r → IntervalPrimeExistsAtPrime q r := by
  intro hPrimeOffset
  exact (intervalPrimeExistsAtPrime_iff_offsetPrimeExistsAtPrime).2
    (offsetPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime hPrimeOffset)

/-- Conversely, a prime in the Route 2 interval has prime offset above `q`. -/
theorem primeOffsetPrimeExistsAtPrime_of_intervalPrimeExistsAtPrime {q r : Nat}
    (hqr : ConsecutivePrimes q r) :
    IntervalPrimeExistsAtPrime q r → PrimeOffsetPrimeExistsAtPrime q r := by
  intro hInterval
  rcases hInterval with ⟨p, hp, hlow, hhigh⟩
  have hq : Nat.Prime q := hqr.1
  have hprim_le_p : primorial q ≤ p := Nat.le_of_lt
    (lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < 1)) hlow)
  let m := p - primorial q
  have hm_prime : Nat.Prime m := by
    dsimp [m]
    exact prime_sub_primorial_of_interval hqr hp hlow hhigh
  have hm_sum : primorial q + m = p := by
    dsimp [m]
    exact Nat.add_sub_of_le hprim_le_p
  have hm_lt_sq : m < r ^ 2 := by
    dsimp [m]
    exact (Nat.sub_lt_iff_lt_add hprim_le_p).2 (by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhigh)
  have hq_lt_m : q < m := by
    refine lt_of_not_ge ?_
    intro hm_le_q
    have hm_dvd_primorial : m ∣ primorial q :=
      prime_dvd_primorial_of_le hm_prime hm_le_q
    have hm_dvd_p : m ∣ p := by
      have hm_dvd_sum : m ∣ primorial q + m := Nat.dvd_add hm_dvd_primorial (dvd_refl m)
      simpa [hm_sum] using hm_dvd_sum
    rcases (Nat.dvd_prime hp).1 hm_dvd_p with hm_eq_one | hm_eq_p
    · exact hm_prime.ne_one hm_eq_one
    · have hq_dvd_primorial : q ∣ primorial q :=
        prime_dvd_primorial_of_le hq (le_rfl)
      have hq_le_primorial : q ≤ primorial q := Nat.le_of_dvd (primorial_pos q) hq_dvd_primorial
      have hq_lt_sum : q < primorial q + 1 :=
        lt_of_le_of_lt hq_le_primorial (Nat.lt_add_of_pos_right (by decide : 0 < 1))
      have hq_lt_p : q < p := lt_trans hq_lt_sum hlow
      have hp_le_q : p ≤ q := by simpa [hm_eq_p] using hm_le_q
      exact (Nat.not_le_of_lt hq_lt_p) hp_le_q
  refine ⟨m, hm_prime, hq_lt_m, hm_lt_sq, ?_⟩
  simpa [hm_sum] using hp

/-- Route-2 interval existence (as used in `Progress`) in terms of threshold primes. -/
def Route2IntervalPrimeExistence' : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r

/-- Equivalent offset-form route-2 interval existence statement. -/
def Route2OffsetPrimeExistence' : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    OffsetPrimeExistsAtPrime (lastIncludedPrime n) r

/-- Stronger route-2 research target in terms of prime offsets. -/
def Route2PrimeOffsetPrimeExistence' : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    PrimeOffsetPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2IntervalPrimeExistence'_iff_route2OffsetPrimeExistence' :
    Route2IntervalPrimeExistence' ↔ Route2OffsetPrimeExistence' := by
  constructor
  · intro hInt n r hn hqr
    exact (intervalPrimeExistsAtPrime_iff_offsetPrimeExistsAtPrime).1 (hInt n r hn hqr)
  · intro hOff n r hn hqr
    exact (intervalPrimeExistsAtPrime_iff_offsetPrimeExistsAtPrime).2 (hOff n r hn hqr)

theorem route2OffsetPrimeExistence'_of_route2PrimeOffsetPrimeExistence' :
    Route2PrimeOffsetPrimeExistence' → Route2OffsetPrimeExistence' := by
  intro hPrimeOffset n r hn hqr
  exact offsetPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime
    (hPrimeOffset n r hn hqr)

theorem route2PrimeOffsetPrimeExistence'_of_route2IntervalPrimeExistence' :
    Route2IntervalPrimeExistence' → Route2PrimeOffsetPrimeExistence' := by
  intro hInterval n r hn hqr
  exact primeOffsetPrimeExistsAtPrime_of_intervalPrimeExistsAtPrime hqr
    (hInterval n r hn hqr)

/-- Route 2 converse direction:
the quantitative reduction bound implies interval-prime existence. -/
theorem intervalPrimeExistence_of_reductionBound
    (hBound :
      ∀ n m r : Nat, 1 ≤ n →
        IsLeastFortunateOffset n m →
        ConsecutivePrimes (lastIncludedPrime n) r →
        m < r ^ 2) :
    ∀ n r : Nat, 1 ≤ n →
      ConsecutivePrimes (lastIncludedPrime n) r →
      ∃ p : Nat, Nat.Prime p ∧
        primorial (lastIncludedPrime n) + 1 < p ∧
        p < primorial (lastIncludedPrime n) + r ^ 2 := by
  intro n r hn hqr
  obtain ⟨m, hLeast⟩ := exists_leastFortunateOffset n
  have hm_lt : m < r ^ 2 := hBound n m r hn hLeast hqr
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn).1 hLeast
  refine ⟨primorial (lastIncludedPrime n) + m, hLeastAtPrime.1.2, ?_, ?_⟩
  · exact Nat.add_lt_add_left hLeastAtPrime.1.1 (primorial (lastIncludedPrime n))
  · exact Nat.add_lt_add_left hm_lt (primorial (lastIncludedPrime n))

/-- Route 2 equivalence: interval-prime existence and reduction bound are equivalent. -/
theorem intervalPrimeExistence_iff_reductionBound :
    (∀ n r : Nat, 1 ≤ n →
      ConsecutivePrimes (lastIncludedPrime n) r →
      ∃ p : Nat, Nat.Prime p ∧
        primorial (lastIncludedPrime n) + 1 < p ∧
        p < primorial (lastIncludedPrime n) + r ^ 2) ↔
    (∀ n m r : Nat, 1 ≤ n →
      IsLeastFortunateOffset n m →
      ConsecutivePrimes (lastIncludedPrime n) r →
      m < r ^ 2) := by
  constructor
  · intro hInt
    exact reduction_bound_of_intervalPrimeExists_at_lastIncluded hInt
  · intro hBound
    exact intervalPrimeExistence_of_reductionBound hBound

end Fortune
