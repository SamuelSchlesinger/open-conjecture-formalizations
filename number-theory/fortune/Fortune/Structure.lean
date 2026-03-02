import Fortune.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Fortune

theorem nthPrime_prime (i : Nat) : Nat.Prime (nthPrime i) := by
  simpa [nthPrime] using
    (Nat.nth_mem_of_infinite (p := Nat.Prime) Nat.infinite_setOf_prime i)

theorem nthPrime_two_le (i : Nat) : 2 ≤ nthPrime i :=
  (nthPrime_prime i).two_le

theorem nthPrimorial_pos (n : Nat) : 0 < nthPrimorial n := by
  induction n with
  | zero =>
      simp [nthPrimorial]
  | succ n ih =>
      rw [nthPrimorial, Finset.prod_range_succ]
      exact Nat.mul_pos ih (lt_of_lt_of_le (by decide : 0 < 2) (nthPrime_two_le n))

theorem nthPrimorial_ne_zero (n : Nat) : nthPrimorial n ≠ 0 :=
  (nthPrimorial_pos n).ne'

theorem nthPrime_dvd_nthPrimorial {n i : Nat} (hi : i < n) :
    nthPrime i ∣ nthPrimorial n := by
  have hi_mem : i ∈ Finset.range n := Finset.mem_range.mpr hi
  simpa [nthPrimorial] using (Finset.dvd_prod_of_mem nthPrime hi_mem)

theorem fortunateOffset_coprime_nthPrimorial {n m : Nat} (h : IsFortunateOffset n m) :
    Nat.Coprime m (nthPrimorial n) := by
  rcases h with ⟨hm_gt_one, hprime_sum⟩
  have hN_pos : 0 < nthPrimorial n := nthPrimorial_pos n
  have hm_lt_sum : m < nthPrimorial n + m := Nat.lt_add_of_pos_left hN_pos
  have hgcd_dvd_sum : Nat.gcd m (nthPrimorial n) ∣ nthPrimorial n + m := by
    exact Nat.dvd_add (Nat.gcd_dvd_right m (nthPrimorial n)) (Nat.gcd_dvd_left m (nthPrimorial n))
  rcases (Nat.dvd_prime hprime_sum).1 hgcd_dvd_sum with hgcd_one | hgcd_eq_sum
  · exact Nat.coprime_iff_gcd_eq_one.mpr hgcd_one
  · exfalso
    have hm_pos : 0 < m := lt_trans (by decide : 0 < 1) hm_gt_one
    have hgcd_le_m : Nat.gcd m (nthPrimorial n) ≤ m := Nat.gcd_le_left (nthPrimorial n) hm_pos
    have hgcd_lt_sum : Nat.gcd m (nthPrimorial n) < nthPrimorial n + m :=
      lt_of_le_of_lt hgcd_le_m hm_lt_sum
    have hsum_lt_self : nthPrimorial n + m < nthPrimorial n + m := by
      simpa [hgcd_eq_sum] using hgcd_lt_sum
    exact (Nat.lt_irrefl (nthPrimorial n + m)) hsum_lt_self

theorem fortunateOffset_not_dvd_nthPrime {n m i : Nat}
    (h : IsFortunateOffset n m) (hi : i < n) :
    ¬ nthPrime i ∣ m := by
  intro hdiv_m
  have hdiv_N : nthPrime i ∣ nthPrimorial n := nthPrime_dvd_nthPrimorial hi
  have hdiv_gcd : nthPrime i ∣ Nat.gcd m (nthPrimorial n) := Nat.dvd_gcd hdiv_m hdiv_N
  have hgcd_eq_one : Nat.gcd m (nthPrimorial n) = 1 :=
    (Nat.coprime_iff_gcd_eq_one).1 (fortunateOffset_coprime_nthPrimorial h)
  have hdiv_one : nthPrime i ∣ 1 := by simpa [hgcd_eq_one] using hdiv_gcd
  exact (nthPrime_prime i).not_dvd_one hdiv_one

theorem fortunateOffset_not_dvd_firstPrimes {n m : Nat}
    (h : IsFortunateOffset n m) :
    ∀ i : Nat, i < n → ¬ nthPrime i ∣ m := by
  intro i hi
  exact fortunateOffset_not_dvd_nthPrime h hi

theorem nthPrimorial_even_of_one_le {n : Nat} (hn : 1 ≤ n) :
    Even (nthPrimorial n) := by
  have h0lt : 0 < n := Nat.succ_le_iff.mp hn
  have h2dvd : 2 ∣ nthPrimorial n := by
    simpa [nthPrime, Nat.nth_prime_zero_eq_two] using
      (nthPrime_dvd_nthPrimorial (n := n) (i := 0) h0lt)
  exact (even_iff_two_dvd).2 h2dvd

theorem fortunateOffset_odd_of_one_le {n m : Nat}
    (hn : 1 ≤ n) (h : IsFortunateOffset n m) :
    Odd m := by
  rcases h with ⟨hm_gt_one, hprime_sum⟩
  have hN_even : Even (nthPrimorial n) := nthPrimorial_even_of_one_le hn
  have hN_pos : 0 < nthPrimorial n := nthPrimorial_pos n
  have hm_ge_two : 2 ≤ m := Nat.succ_le_of_lt hm_gt_one
  have hsum_gt_two : 2 < nthPrimorial n + m := by
    have hN_ge_two : 2 ≤ nthPrimorial n := Nat.le_of_dvd hN_pos ((even_iff_two_dvd).1 hN_even)
    have hfour_le : 4 ≤ nthPrimorial n + m := Nat.add_le_add hN_ge_two hm_ge_two
    exact lt_of_lt_of_le (by decide : 2 < 4) hfour_le
  have hm_not_even : ¬Even m := by
    intro hm_even
    have hsum_even : Even (nthPrimorial n + m) := hN_even.add hm_even
    have hsum_eq_two : nthPrimorial n + m = 2 := (hprime_sum.even_iff).1 hsum_even
    have htwo_lt_two : 2 < 2 := by simpa [hsum_eq_two] using hsum_gt_two
    exact (Nat.lt_irrefl 2) htwo_lt_two
  exact (Nat.not_even_iff_odd).1 hm_not_even

end Fortune
