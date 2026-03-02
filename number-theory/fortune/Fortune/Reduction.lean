import Fortune.Bridge
import Fortune.Existence

namespace Fortune

/-- Under the Route 2.A quantitative bound hypothesis, any indexed least Fortunate
offset is prime. -/
theorem leastOffset_prime_of_reduction_bound
    (hBound :
      ∀ n m r : Nat, 1 ≤ n →
        IsLeastFortunateOffset n m →
        ConsecutivePrimes (lastIncludedPrime n) r →
        m < r ^ 2)
    {n m : Nat} (hn : 1 ≤ n) (hLeast : IsLeastFortunateOffset n m) :
    Nat.Prime m := by
  obtain ⟨r, hqr⟩ := bridge_exists_nextPrime_at_lastIncluded n hn
  have hm_lt : m < r ^ 2 := hBound n m r hn hLeast hqr
  have hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m :=
    (bridge_leastOffset_indexed_to_threshold n m hn).1 hLeast
  exact least_offset_prime_of_lt_nextPrime_sq hqr hLeastAtPrime hm_lt

/-- Route 2.B reduction theorem:
the Route 2.A quantitative bound implies `FortuneConjecture`. -/
theorem reduction_bound_implies_fortune
    (hBound :
      ∀ n m r : Nat, 1 ≤ n →
        IsLeastFortunateOffset n m →
        ConsecutivePrimes (lastIncludedPrime n) r →
        m < r ^ 2) :
    FortuneConjecture := by
  intro n hn
  obtain ⟨m, hmLeast⟩ := exists_leastFortunateOffset n
  exact ⟨m, hmLeast, leastOffset_prime_of_reduction_bound hBound hn hmLeast⟩

end Fortune
