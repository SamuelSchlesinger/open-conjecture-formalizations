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

theorem route2IntervalPrimeExistence'_iff_route2OffsetPrimeExistence' :
    Route2IntervalPrimeExistence' ↔ Route2OffsetPrimeExistence' := by
  constructor
  · intro hInt n r hn hqr
    exact (intervalPrimeExistsAtPrime_iff_offsetPrimeExistsAtPrime).1 (hInt n r hn hqr)
  · intro hOff n r hn hqr
    exact (intervalPrimeExistsAtPrime_iff_offsetPrimeExistsAtPrime).2 (hOff n r hn hqr)

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
