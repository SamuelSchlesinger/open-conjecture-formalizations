import Fortune.Bridge
import Mathlib.Data.Nat.ModEq

namespace Fortune

/-- For any prime included in the `n`-primorial, `nthPrimorial n + m` is congruent to `m`
modulo that prime. -/
theorem nthPrimorial_add_modEq_offset_nthPrime {n m i : Nat} (hi : i < n) :
    nthPrimorial n + m ≡ m [MOD nthPrime i] := by
  have hdiv : nthPrime i ∣ nthPrimorial n := nthPrime_dvd_nthPrimorial hi
  have hzero : nthPrimorial n ≡ 0 [MOD nthPrime i] := (Nat.modEq_zero_iff_dvd).2 hdiv
  simpa using hzero.add (Nat.ModEq.refl m)

/-- Congruence obstruction (indexed form): no prime among the first `n` primes can divide
a Fortunate offset. -/
theorem fortunateOffset_not_modEq_zero_nthPrime {n m i : Nat}
    (hOffset : IsFortunateOffset n m) (hi : i < n) :
    ¬ m ≡ 0 [MOD nthPrime i] := by
  intro hmod
  exact fortunateOffset_not_dvd_nthPrime hOffset hi ((Nat.modEq_zero_iff_dvd).1 hmod)

/-- Congruence obstruction for least indexed offsets. -/
theorem leastFortunateOffset_not_modEq_zero_nthPrime {n m i : Nat}
    (hLeast : IsLeastFortunateOffset n m) (hi : i < n) :
    ¬ m ≡ 0 [MOD nthPrime i] :=
  fortunateOffset_not_modEq_zero_nthPrime hLeast.1 hi

/-- Congruence obstruction (threshold form):
if `t` is prime and `t ≤ q`, then `t` cannot divide a Fortunate offset at `q`. -/
theorem fortunateOffsetAtPrime_not_modEq_zero_of_prime_le {q m t : Nat}
    (hOffset : IsFortunateOffsetAtPrime q m)
    (htPrime : Nat.Prime t) (ht_le : t ≤ q) :
    ¬ m ≡ 0 [MOD t] := by
  intro hmod
  have htdvd_m : t ∣ m := (Nat.modEq_zero_iff_dvd).1 hmod
  have htdvd_primorial : t ∣ primorial q := prime_dvd_primorial_of_le htPrime ht_le
  have htdvd_sum : t ∣ primorial q + m := Nat.dvd_add htdvd_primorial htdvd_m
  rcases (Nat.dvd_prime hOffset.2).1 htdvd_sum with ht_one | ht_eq_sum
  · exact htPrime.ne_one ht_one
  · have ht_le_primorial : t ≤ primorial q := Nat.le_of_dvd (primorial_pos q) htdvd_primorial
    have hm_pos : 0 < m := lt_trans (by decide : 0 < 1) hOffset.1
    have ht_lt_sum : t < primorial q + m := lt_of_le_of_lt ht_le_primorial
      (Nat.lt_add_of_pos_right hm_pos)
    have hsum_lt_self : primorial q + m < primorial q + m := by
      calc
        primorial q + m = t := by exact ht_eq_sum.symm
        _ < primorial q + m := ht_lt_sum
    exact (Nat.lt_irrefl (primorial q + m)) hsum_lt_self

/-- Congruence obstruction for least threshold offsets. -/
theorem leastOffsetAtPrime_not_modEq_zero_of_prime_le {q m t : Nat}
    (hLeast : IsLeastFortunateOffsetAtPrime q m)
    (htPrime : Nat.Prime t) (ht_le : t ≤ q) :
    ¬ m ≡ 0 [MOD t] :=
  fortunateOffsetAtPrime_not_modEq_zero_of_prime_le hLeast.1 htPrime ht_le

/-- Bridged congruence obstruction at `lastIncludedPrime n` for the indexed prime list. -/
theorem leastOffsetAtLastIncludedPrime_not_modEq_zero_nthPrime {n m i : Nat}
    (hn : 1 ≤ n)
    (hLeastAtPrime : IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m)
    (hi : i < n) :
    ¬ m ≡ 0 [MOD nthPrime i] := by
  have hLeastIndexed : IsLeastFortunateOffset n m :=
    (bridge_leastOffset_indexed_to_threshold n m hn).2 hLeastAtPrime
  exact leastFortunateOffset_not_modEq_zero_nthPrime hLeastIndexed hi

end Fortune
