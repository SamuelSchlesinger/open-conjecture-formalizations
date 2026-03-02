import Fortune.Defs
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Fortune

/-- `q < r` are consecutive primes if there are no primes strictly between them. -/
def ConsecutivePrimes (q r : Nat) : Prop :=
  Nat.Prime q ∧ Nat.Prime r ∧ q < r ∧ ∀ t : Nat, Nat.Prime t → q < t → t < r → False

/-- Prime divisibility into primorial by order bound. -/
theorem prime_dvd_primorial_of_le {p q : Nat} (hp : Nat.Prime p) (hpq : p ≤ q) :
    p ∣ primorial q := by
  unfold primorial
  refine Finset.dvd_prod_of_mem (fun n => n) ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpq), hp⟩

/-- A primorial version of Čejchan–Křížek–Somer Theorem 17:
if `p` is prime and lies in `(q# + 1, q# + r^2)` where `r` is the next prime after `q`,
then `p - q#` is prime. -/
theorem prime_sub_primorial_of_interval {q r p : Nat}
    (hqr : ConsecutivePrimes q r)
    (hp : Nat.Prime p)
    (hlow : primorial q + 1 < p)
    (hhigh : p < primorial q + r ^ 2) :
    Nat.Prime (p - primorial q) := by
  rcases hqr with ⟨hq, hr, hq_lt_r, hno_between⟩
  have hprim_le_p : primorial q ≤ p := Nat.le_of_lt (lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < 1)) hlow)
  have htwo_le_sub : 2 ≤ p - primorial q := by
    have htwo_plus_prim_le_p : 2 + primorial q ≤ p := by
      have : primorial q + 2 ≤ p := Nat.succ_le_of_lt hlow
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    exact Nat.le_sub_of_add_le htwo_plus_prim_le_p
  have hone_lt_sub : 1 < p - primorial q := lt_of_lt_of_le (by decide : 1 < 2) htwo_le_sub
  by_contra hsub_prime
  have hsub_not_prime : ¬Nat.Prime (p - primorial q) := hsub_prime
  let m := Nat.minFac (p - primorial q)
  have hm_prime : Nat.Prime m := by
    exact Nat.minFac_prime (n := p - primorial q) (ne_of_gt hone_lt_sub)
  have hm_dvd_sub : m ∣ p - primorial q := by
    exact Nat.minFac_dvd (p - primorial q)
  have hm_gt_q : q < m := by
    refine lt_of_not_ge ?_
    intro hm_le_q
    have hm_dvd_prim : m ∣ primorial q := prime_dvd_primorial_of_le hm_prime hm_le_q
    have hm_dvd_p : m ∣ p := by
      have hm_dvd_sum : m ∣ primorial q + (p - primorial q) := Nat.dvd_add hm_dvd_prim hm_dvd_sub
      simpa [Nat.add_sub_of_le hprim_le_p, Nat.add_comm] using hm_dvd_sum
    rcases (Nat.dvd_prime hp).1 hm_dvd_p with hm_one | hm_eq_p
    · exact hm_prime.ne_one hm_one
    · have hq_lt_p : q < p := by
        have hq_dvd_prim : q ∣ primorial q := prime_dvd_primorial_of_le hq (le_rfl)
        have hq_le_prim : q ≤ primorial q := Nat.le_of_dvd (primorial_pos q) hq_dvd_prim
        have hq_lt_prim_plus_one : q < primorial q + 1 :=
          lt_of_le_of_lt hq_le_prim (Nat.lt_add_of_pos_right (by decide : 0 < 1))
        exact lt_trans hq_lt_prim_plus_one hlow
      have hp_le_q : p ≤ q := by simpa [hm_eq_p] using hm_le_q
      exact (Nat.not_le_of_lt hq_lt_p) hp_le_q
  have hsub_pos : 0 < p - primorial q := lt_trans (by decide : 0 < 1) hone_lt_sub
  have hm_sq_le_sub : m ^ 2 ≤ p - primorial q := Nat.minFac_sq_le_self hsub_pos hsub_not_prime
  have hsub_lt_rsq : p - primorial q < r ^ 2 := by
    exact (Nat.sub_lt_iff_lt_add hprim_le_p).2 (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hhigh)
  have hm_sq_lt_rsq : m ^ 2 < r ^ 2 := lt_of_le_of_lt hm_sq_le_sub hsub_lt_rsq
  have hm_lt_r : m < r := (Nat.pow_lt_pow_iff_left (by decide : (2 : Nat) ≠ 0)).1 hm_sq_lt_rsq
  exact hno_between m hm_prime hm_gt_q hm_lt_r

/-- A primorial/Fortunate corollary of `prime_sub_primorial_of_interval`:
if the least Fortunate offset at prime `q` is below `r^2` (where `r` is the next prime after `q`),
then that offset is prime. -/
def IsFortunateOffsetAtPrime (q m : Nat) : Prop :=
  1 < m ∧ Nat.Prime (primorial q + m)

def IsLeastFortunateOffsetAtPrime (q m : Nat) : Prop :=
  IsFortunateOffsetAtPrime q m ∧
    ∀ k : Nat, 1 < k → k < m → ¬Nat.Prime (primorial q + k)

theorem least_offset_prime_of_lt_nextPrime_sq {q r m : Nat}
    (hqr : ConsecutivePrimes q r)
    (hmLeast : IsLeastFortunateOffsetAtPrime q m)
    (hm_lt : m < r ^ 2) :
    Nat.Prime m := by
  have hmOffset : IsFortunateOffsetAtPrime q m := hmLeast.1
  have hprime_p : Nat.Prime (primorial q + m) := hmOffset.2
  have hlow : primorial q + 1 < primorial q + m := Nat.add_lt_add_left hmOffset.1 (primorial q)
  have hhigh : primorial q + m < primorial q + r ^ 2 := Nat.add_lt_add_left hm_lt (primorial q)
  have hsub_prime : Nat.Prime ((primorial q + m) - primorial q) :=
    prime_sub_primorial_of_interval hqr hprime_p hlow hhigh
  simpa [Nat.add_sub_cancel_left] using hsub_prime

/-- A machine-checkable variant of Čejchan–Křížek–Somer Theorem 18:
if `s < q` are consecutive primes and `p` is prime in `(q# - s^2, q# - 1)` with `q < p`,
then `q# - p` is prime. -/
theorem prime_primorial_sub_of_interval {s q p : Nat}
    (hsq : ConsecutivePrimes s q)
    (hp : Nat.Prime p)
    (hq_lt_p : q < p)
    (hlow : primorial q - s ^ 2 < p)
    (hhigh : p < primorial q - 1) :
    Nat.Prime (primorial q - p) := by
  rcases hsq with ⟨hs, hq, hs_lt_q, hno_between⟩
  have hp_le_prim : p ≤ primorial q := by omega
  have htwo_le_sub : 2 ≤ primorial q - p := by omega
  have hone_lt_sub : 1 < primorial q - p := lt_of_lt_of_le (by decide : 1 < 2) htwo_le_sub
  by_contra hsub_prime
  have hsub_not_prime : ¬Nat.Prime (primorial q - p) := hsub_prime
  let m := Nat.minFac (primorial q - p)
  have hm_prime : Nat.Prime m := by
    exact Nat.minFac_prime (n := primorial q - p) (ne_of_gt hone_lt_sub)
  have hm_dvd_sub : m ∣ primorial q - p := by
    exact Nat.minFac_dvd (primorial q - p)
  have hq_lt_m : q < m := by
    refine lt_of_not_ge ?_
    intro hm_le_q
    have hm_dvd_prim : m ∣ primorial q := prime_dvd_primorial_of_le hm_prime hm_le_q
    have hm_dvd_p : m ∣ p := (Nat.dvd_sub_iff_right hp_le_prim hm_dvd_prim).1 hm_dvd_sub
    rcases (Nat.dvd_prime hp).1 hm_dvd_p with hm_one | hm_eq_p
    · exact hm_prime.ne_one hm_one
    · have hp_le_q : p ≤ q := by simpa [hm_eq_p] using hm_le_q
      exact (Nat.not_le_of_lt hq_lt_p) hp_le_q
  have hsub_pos : 0 < primorial q - p := lt_trans (by decide : 0 < 1) hone_lt_sub
  have hm_sq_le_sub : m ^ 2 ≤ primorial q - p := Nat.minFac_sq_le_self hsub_pos hsub_not_prime
  have hsub_lt_ssq : primorial q - p < s ^ 2 := by omega
  have hm_sq_lt_ssq : m ^ 2 < s ^ 2 := lt_of_le_of_lt hm_sq_le_sub hsub_lt_ssq
  have hm_lt_s : m < s := (Nat.pow_lt_pow_iff_left (by decide : (2 : Nat) ≠ 0)).1 hm_sq_lt_ssq
  have hq_lt_s : q < s := lt_trans hq_lt_m hm_lt_s
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hs_lt_q)) hq_lt_s

end Fortune
