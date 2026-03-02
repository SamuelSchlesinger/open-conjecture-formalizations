import Fortune.Bridge

namespace Fortune

/-- If `m` is a least Fortunate offset at threshold `q`, then any other
admissible prime-yielding candidate offset `k > 1` is at least `m`. -/
theorem leastOffsetAtPrime_le_of_primeCandidate {q m k : Nat}
    (hLeast : IsLeastFortunateOffsetAtPrime q m)
    (hk_gt_one : 1 < k)
    (hk_prime_sum : Nat.Prime (primorial q + k)) :
    m ≤ k := by
  by_contra hmk
  have hk_lt_m : k < m := Nat.lt_of_not_ge hmk
  exact (hLeast.2 k hk_gt_one hk_lt_m) hk_prime_sum

/-- A prime in the upper primorial interval yields a candidate offset
`k < r^2` with `primorial q + k` prime. -/
theorem primeCandidate_lt_nextPrime_sq_of_interval {q r p : Nat}
    (hqr : ConsecutivePrimes q r)
    (hp : Nat.Prime p)
    (hlow : primorial q + 1 < p)
    (hhigh : p < primorial q + r ^ 2) :
    ∃ k : Nat, 1 < k ∧ k < r ^ 2 ∧ Nat.Prime (primorial q + k) := by
  have hprim_le_p : primorial q ≤ p := Nat.le_of_lt
    (lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < 1)) hlow)
  refine ⟨p - primorial q, ?_, ?_, ?_⟩
  · have hk_prime : Nat.Prime (p - primorial q) :=
      prime_sub_primorial_of_interval hqr hp hlow hhigh
    exact lt_of_lt_of_le (by decide : 1 < 2) hk_prime.two_le
  · exact (Nat.sub_lt_iff_lt_add hprim_le_p).2 (by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhigh)
  · have hsum : primorial q + (p - primorial q) = p := Nat.add_sub_of_le hprim_le_p
    simpa [hsum] using hp

/-- If there exists a prime in the upper primorial interval at threshold `q`,
then any least Fortunate offset at `q` is below `r^2`. -/
theorem leastOffsetAtPrime_lt_nextPrime_sq_of_intervalPrime
    {q r m p : Nat}
    (hqr : ConsecutivePrimes q r)
    (hLeast : IsLeastFortunateOffsetAtPrime q m)
    (hp : Nat.Prime p)
    (hlow : primorial q + 1 < p)
    (hhigh : p < primorial q + r ^ 2) :
    m < r ^ 2 := by
  obtain ⟨k, hk_gt_one, hk_lt_sq, hk_prime_sum⟩ :=
    primeCandidate_lt_nextPrime_sq_of_interval hqr hp hlow hhigh
  have hm_le_k : m ≤ k :=
    leastOffsetAtPrime_le_of_primeCandidate hLeast hk_gt_one hk_prime_sum
  exact lt_of_le_of_lt hm_le_k hk_lt_sq

/-- Conditional Route 2.A:
if each `lastIncludedPrime n` interval `(q# + 1, q# + r^2)` contains a prime
for consecutive-prime witnesses `q < r`, then the Route 2.A quantitative bound holds. -/
theorem reduction_bound_of_intervalPrimeExists_at_lastIncluded
    (hInterval :
      ∀ n r : Nat, 1 ≤ n →
        ConsecutivePrimes (lastIncludedPrime n) r →
        ∃ p : Nat, Nat.Prime p ∧
          primorial (lastIncludedPrime n) + 1 < p ∧
          p < primorial (lastIncludedPrime n) + r ^ 2) :
    ∀ n m r : Nat, 1 ≤ n →
      IsLeastFortunateOffset n m →
      ConsecutivePrimes (lastIncludedPrime n) r →
      m < r ^ 2 := by
  intro n m r hn hLeast hqr
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn).1 hLeast
  rcases hInterval n r hn hqr with ⟨p, hp, hlow, hhigh⟩
  exact leastOffsetAtPrime_lt_nextPrime_sq_of_intervalPrime hqr hLeastAtPrime hp hlow hhigh

end Fortune
