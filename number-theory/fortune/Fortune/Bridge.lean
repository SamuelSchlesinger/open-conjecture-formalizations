import Fortune.Basic
import Fortune.Structure
import Fortune.Literature
import Mathlib.Tactic

namespace Fortune

/-- Product of the first `k + 1` indexed primes as a product over all primes
strictly below the next indexed prime. -/
theorem nthPrimorial_succ_eq_prod_primes_lt_nthPrime_succ (k : Nat) :
    nthPrimorial (k + 1) =
      ∏ p ∈ Finset.range (nthPrime (k + 1)) with Nat.Prime p, p := by
  induction k with
  | zero =>
      rw [nthPrimorial_one, nthPrime, Nat.nth_prime_one_eq_three]
      native_decide
  | succ k ih =>
      have hset :
          {p ∈ Finset.range (nthPrime (k + 2)) | Nat.Prime p} =
            insert (nthPrime (k + 1))
              {p ∈ Finset.range (nthPrime (k + 1)) | Nat.Prime p} := by
        simpa [nthPrime, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Nat.filter_range_nth_eq_insert_of_infinite
            (p := Nat.Prime) Nat.infinite_setOf_prime (k + 1))
      have hnotmem :
          nthPrime (k + 1) ∉ {p ∈ Finset.range (nthPrime (k + 1)) | Nat.Prime p} := by
        simp
      have hprod :
          (∏ p ∈ Finset.range (nthPrime (k + 2)) with Nat.Prime p, p) =
            nthPrime (k + 1) *
              (∏ p ∈ Finset.range (nthPrime (k + 1)) with Nat.Prime p, p) := by
        rw [hset, Finset.prod_insert hnotmem]
      calc
        nthPrimorial (k + 2) = nthPrimorial (k + 1) * nthPrime (k + 1) := by
          simpa [nthPrimorial, Nat.add_assoc] using
            (Finset.prod_range_succ (f := nthPrime) (n := k + 1))
        _ = (∏ p ∈ Finset.range (nthPrime (k + 1)) with Nat.Prime p, p) * nthPrime (k + 1) := by
          rw [ih]
        _ = nthPrime (k + 1) *
              (∏ p ∈ Finset.range (nthPrime (k + 1)) with Nat.Prime p, p) := by
          rw [Nat.mul_comm]
        _ = (∏ p ∈ Finset.range (nthPrime (k + 2)) with Nat.Prime p, p) := by
          exact hprod.symm

/-- Primorial at `lastIncludedPrime n` as a product over primes below `nthPrime n`. -/
theorem primorial_lastIncludedPrime_eq_prod_primes_lt_nextPrime :
    ∀ n : Nat, 1 ≤ n →
      primorial (lastIncludedPrime n) =
        ∏ p ∈ Finset.range (nthPrime n) with Nat.Prime p, p := by
  intro n hn
  rcases n with _ | k
  · exact (Nat.not_succ_le_zero 0 hn).elim
  · have hset_next :
        {p ∈ Finset.range (nthPrime (k + 1)) | Nat.Prime p} =
          insert (nthPrime k) {p ∈ Finset.range (nthPrime k) | Nat.Prime p} := by
      simpa [nthPrime, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.filter_range_nth_eq_insert_of_infinite
          (p := Nat.Prime) Nat.infinite_setOf_prime k)
    have hset_succ :
        {p ∈ Finset.range (nthPrime k + 1) | Nat.Prime p} =
          insert (nthPrime k) {p ∈ Finset.range (nthPrime k) | Nat.Prime p} := by
      rw [Finset.range_add_one, Finset.filter_insert, if_pos (nthPrime_prime k)]
    have hset :
        {p ∈ Finset.range (nthPrime k + 1) | Nat.Prime p} =
          {p ∈ Finset.range (nthPrime (k + 1)) | Nat.Prime p} :=
      hset_succ.trans hset_next.symm
    have hprod :
        (∏ p ∈ Finset.range (nthPrime k + 1) with Nat.Prime p, p) =
          (∏ p ∈ Finset.range (nthPrime (k + 1)) with Nat.Prime p, p) :=
      congrArg (fun s : Finset Nat => s.prod id) hset
    simpa [primorial, lastIncludedPrime] using hprod

/-- Route 1.A bridge theorem. -/
theorem bridge_nthPrimorial_eq_primorial_lastIncludedPrime :
    ∀ n : Nat, 1 ≤ n → nthPrimorial n = primorial (lastIncludedPrime n) := by
  intro n hn
  rcases n with _ | k
  · exact (Nat.not_succ_le_zero 0 hn).elim
  · calc
      nthPrimorial (k + 1) =
          ∏ p ∈ Finset.range (nthPrime (k + 1)) with Nat.Prime p, p :=
        nthPrimorial_succ_eq_prod_primes_lt_nthPrime_succ k
      _ = primorial (lastIncludedPrime (k + 1)) := by
        exact
          (primorial_lastIncludedPrime_eq_prod_primes_lt_nextPrime (k + 1)
            (Nat.succ_le_succ (Nat.zero_le k))).symm

/-- Indexed and threshold offset predicates agree once Route 1.A is available. -/
theorem bridge_fortunateOffset_indexed_to_threshold
    (n m : Nat) (hn : 1 ≤ n) :
    (IsFortunateOffset n m ↔ IsFortunateOffsetAtPrime (lastIncludedPrime n) m) := by
  have hprimorial := bridge_nthPrimorial_eq_primorial_lastIncludedPrime n hn
  simp [IsFortunateOffset, IsFortunateOffsetAtPrime, hprimorial]

/-- Route 1.B bridge theorem. -/
theorem bridge_leastOffset_indexed_to_threshold :
    ∀ n m : Nat, 1 ≤ n →
      (IsLeastFortunateOffset n m ↔ IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m) := by
  intro n m hn
  have hprimorial := bridge_nthPrimorial_eq_primorial_lastIncludedPrime n hn
  constructor
  · intro hLeast
    rcases hLeast with ⟨hOffset, hMin⟩
    refine ⟨(bridge_fortunateOffset_indexed_to_threshold n m hn).1 hOffset, ?_⟩
    intro k hk_gt_one hk_lt_m
    have hNot : ¬Nat.Prime (nthPrimorial n + k) := hMin k hk_gt_one hk_lt_m
    simpa [hprimorial] using hNot
  · intro hLeast
    rcases hLeast with ⟨hOffset, hMin⟩
    refine ⟨(bridge_fortunateOffset_indexed_to_threshold n m hn).2 hOffset, ?_⟩
    intro k hk_gt_one hk_lt_m
    have hNot : ¬Nat.Prime (primorial (lastIncludedPrime n) + k) := hMin k hk_gt_one hk_lt_m
    simpa [hprimorial] using hNot

/-- Every prime has a next consecutive prime witness. -/
theorem exists_consecutivePrime_after (q : Nat) (hq : Nat.Prime q) :
    ∃ r : Nat, ConsecutivePrimes q r := by
  let hAbove : ∃ r : Nat, Nat.Prime r ∧ q < r := by
    obtain ⟨r, hr_ge, hr_prime⟩ := Nat.exists_infinite_primes (q + 1)
    exact ⟨r, hr_prime, lt_of_lt_of_le (Nat.lt_succ_self q) hr_ge⟩
  refine ⟨Nat.find hAbove, ?_⟩
  refine ⟨hq, (Nat.find_spec hAbove).1, (Nat.find_spec hAbove).2, ?_⟩
  intro t htPrime hq_lt_t ht_lt_find
  have hfind_le_t : Nat.find hAbove ≤ t := Nat.find_min' hAbove ⟨htPrime, hq_lt_t⟩
  exact (Nat.not_le_of_lt ht_lt_find) hfind_le_t

/-- Route 1.C bridge theorem. -/
theorem bridge_exists_nextPrime_at_lastIncluded :
    ∀ n : Nat, 1 ≤ n → ∃ r : Nat, ConsecutivePrimes (lastIncludedPrime n) r := by
  intro n _hn
  have hq : Nat.Prime (lastIncludedPrime n) := by
    unfold lastIncludedPrime
    exact nthPrime_prime (n - 1)
  exact exists_consecutivePrime_after (lastIncludedPrime n) hq

end Fortune
