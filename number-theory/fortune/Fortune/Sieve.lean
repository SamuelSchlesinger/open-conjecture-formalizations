import Fortune.IntervalExistence
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

namespace Fortune

/-- A prime offset `m` in the Route 2 range whose translate `q# + m`
has no proper prime divisor up to the sieve level `z`. -/
def SiftedPrimeOffsetCandidateAtPrime (q r z m : Nat) : Prop :=
  Nat.Prime m ∧
    q < m ∧
    m < r ^ 2 ∧
    ∀ ℓ : Nat, Nat.Prime ℓ → ℓ ≤ z → ℓ ∣ primorial q + m → ℓ = primorial q + m

/-- Existence of a sifted prime-offset candidate at threshold `q`. -/
def SiftedPrimeOffsetExistsAtPrime (q r z : Nat) : Prop :=
  ∃ m : Nat, SiftedPrimeOffsetCandidateAtPrime q r z m

/-- For a prime offset `m > q`, no prime `ℓ ≤ q` can divide `q# + m`. -/
theorem primeOffset_not_dvd_primorial_add_of_prime_le {q m ℓ : Nat}
    (hmPrime : Nat.Prime m)
    (hq_lt_m : q < m)
    (hℓPrime : Nat.Prime ℓ)
    (hℓ_le_q : ℓ ≤ q) :
    ¬ ℓ ∣ primorial q + m := by
  intro hℓ_dvd_sum
  have hℓ_dvd_primorial : ℓ ∣ primorial q := prime_dvd_primorial_of_le hℓPrime hℓ_le_q
  have hℓ_dvd_sum' : ℓ ∣ m + primorial q := by
    simpa [Nat.add_comm] using hℓ_dvd_sum
  have hℓ_dvd_m : ℓ ∣ m := (Nat.dvd_add_left hℓ_dvd_primorial).1 hℓ_dvd_sum'
  rcases (Nat.dvd_prime hmPrime).1 hℓ_dvd_m with hℓ_eq_one | hℓ_eq_m
  · exact hℓPrime.ne_one hℓ_eq_one
  · exact (Nat.ne_of_lt (lt_of_le_of_lt hℓ_le_q hq_lt_m)) hℓ_eq_m

/-- Windowed sieve formulation: only primes strictly above `q` need to be checked,
because primes `≤ q` are already excluded by the primorial congruence structure. -/
def WindowSiftedPrimeOffsetCandidateAtPrime (q r z m : Nat) : Prop :=
  Nat.Prime m ∧
    q < m ∧
    m < r ^ 2 ∧
    ∀ ℓ : Nat, Nat.Prime ℓ → q < ℓ → ℓ ≤ z → ℓ ∣ primorial q + m → ℓ = primorial q + m

/-- Existence of a window-sifted prime-offset candidate. -/
def WindowSiftedPrimeOffsetExistsAtPrime (q r z : Nat) : Prop :=
  ∃ m : Nat, WindowSiftedPrimeOffsetCandidateAtPrime q r z m

/-- Windowed roughness formulation:
no prime divisor of `q# + m` appears in the sieve window `q < ℓ ≤ z`. -/
def WindowRoughPrimeOffsetCandidateAtPrime (q r z m : Nat) : Prop :=
  Nat.Prime m ∧
    q < m ∧
    m < r ^ 2 ∧
    ∀ ℓ : Nat, Nat.Prime ℓ → q < ℓ → ℓ ≤ z → ¬ ℓ ∣ primorial q + m

/-- Existence of a window-rough prime-offset candidate. -/
def WindowRoughPrimeOffsetExistsAtPrime (q r z : Nat) : Prop :=
  ∃ m : Nat, WindowRoughPrimeOffsetCandidateAtPrime q r z m

/-- The full and windowed sieve candidates are equivalent. -/
theorem siftedPrimeOffsetCandidateAtPrime_iff_windowSiftedPrimeOffsetCandidateAtPrime
    {q r z m : Nat} :
    SiftedPrimeOffsetCandidateAtPrime q r z m ↔
      WindowSiftedPrimeOffsetCandidateAtPrime q r z m := by
  constructor
  · intro h
    rcases h with ⟨hmPrime, hq_lt_m, hm_lt_sq, hSifted⟩
    refine ⟨hmPrime, hq_lt_m, hm_lt_sq, ?_⟩
    intro ℓ hℓPrime hq_lt_ℓ hℓ_le_z hℓ_dvd_sum
    exact hSifted ℓ hℓPrime hℓ_le_z hℓ_dvd_sum
  · intro h
    rcases h with ⟨hmPrime, hq_lt_m, hm_lt_sq, hWindow⟩
    refine ⟨hmPrime, hq_lt_m, hm_lt_sq, ?_⟩
    intro ℓ hℓPrime hℓ_le_z hℓ_dvd_sum
    by_cases hq_lt_ℓ : q < ℓ
    · exact hWindow ℓ hℓPrime hq_lt_ℓ hℓ_le_z hℓ_dvd_sum
    · exact False.elim <|
        primeOffset_not_dvd_primorial_add_of_prime_le hmPrime hq_lt_m hℓPrime
          (Nat.le_of_not_gt hq_lt_ℓ) hℓ_dvd_sum

/-- The existential full and windowed sieve formulations are equivalent. -/
theorem siftedPrimeOffsetExistsAtPrime_iff_windowSiftedPrimeOffsetExistsAtPrime
    {q r z : Nat} :
    SiftedPrimeOffsetExistsAtPrime q r z ↔
      WindowSiftedPrimeOffsetExistsAtPrime q r z := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (siftedPrimeOffsetCandidateAtPrime_iff_windowSiftedPrimeOffsetCandidateAtPrime).1 hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (siftedPrimeOffsetCandidateAtPrime_iff_windowSiftedPrimeOffsetCandidateAtPrime).2 hm⟩

/-- If the sieve level stays strictly below the translate, the window-sifted and
window-rough formulations coincide. -/
theorem windowRoughPrimeOffsetCandidateAtPrime_of_windowSiftedPrimeOffsetCandidateAtPrime
    {q r z m : Nat}
    (hCand : WindowSiftedPrimeOffsetCandidateAtPrime q r z m)
    (hz_lt : z < primorial q + m) :
    WindowRoughPrimeOffsetCandidateAtPrime q r z m := by
  rcases hCand with ⟨hmPrime, hq_lt_m, hm_lt_sq, hSifted⟩
  refine ⟨hmPrime, hq_lt_m, hm_lt_sq, ?_⟩
  intro ℓ hℓPrime hq_lt_ℓ hℓ_le_z hℓ_dvd_sum
  have hℓ_eq_sum : ℓ = primorial q + m :=
    hSifted ℓ hℓPrime hq_lt_ℓ hℓ_le_z hℓ_dvd_sum
  have hℓ_lt_sum : ℓ < primorial q + m := lt_of_le_of_lt hℓ_le_z hz_lt
  exact (Nat.ne_of_lt hℓ_lt_sum) hℓ_eq_sum

/-- The natural "full sieve" level attached to the Route 2 interval. -/
def fullSieveLevelAtPrime (q r : Nat) : Nat :=
  primorial q + r ^ 2

/-- Euclid-style upper bound on the next consecutive prime after `q`. -/
theorem nextPrime_le_primorial_add_one {q r : Nat}
    (hqr : ConsecutivePrimes q r) :
    r ≤ primorial q + 1 := by
  rcases hqr with ⟨hq, hr, hq_lt_r, hno_between⟩
  let p := Nat.minFac (primorial q + 1)
  have hp_sum_ne_one : primorial q + 1 ≠ 1 := by
    have hprim_pos : 0 < primorial q := primorial_pos q
    omega
  have hp_prime : Nat.Prime p := Nat.minFac_prime hp_sum_ne_one
  have hp_dvd_sum : p ∣ primorial q + 1 := Nat.minFac_dvd (primorial q + 1)
  have hq_lt_p : q < p := by
    refine lt_of_not_ge ?_
    intro hp_le_q
    have hp_dvd_primorial : p ∣ primorial q :=
      prime_dvd_primorial_of_le hp_prime hp_le_q
    have hp_dvd_one : p ∣ 1 := (Nat.dvd_add_iff_right hp_dvd_primorial).2 hp_dvd_sum
    exact hp_prime.not_dvd_one hp_dvd_one
  have hr_le_p : r ≤ p := by
    refine le_of_not_gt ?_
    intro hp_lt_r
    exact hno_between p hp_prime hq_lt_p hp_lt_r
  have hp_le_sum : p ≤ primorial q + 1 := Nat.minFac_le (Nat.succ_pos _)
  exact le_trans hr_le_p hp_le_sum

/-- Canonical square-root-scale sieve level attached to the Route 2 interval. -/
def canonicalSquareSieveLevelAtPrime (q r : Nat) : Nat :=
  Nat.sqrt (fullSieveLevelAtPrime q r) + 1

theorem fullSieveLevelAtPrime_le_canonicalSquareSieveLevelAtPrime_sq {q r : Nat} :
    fullSieveLevelAtPrime q r ≤ canonicalSquareSieveLevelAtPrime q r ^ 2 := by
  unfold canonicalSquareSieveLevelAtPrime
  exact le_trans (Nat.le_succ _) (Nat.succ_le_succ_sqrt' (fullSieveLevelAtPrime q r))

theorem canonicalSquareSieveLevelAtPrime_lt_translate_of_consecutivePrimes {q r m : Nat}
    (hqr : ConsecutivePrimes q r)
    (hq_lt_m : q < m) :
    canonicalSquareSieveLevelAtPrime q r < primorial q + m := by
  have hq : Nat.Prime q := hqr.1
  have hr_le : r ≤ primorial q + 1 := nextPrime_le_primorial_add_one hqr
  have hr_sq_le : r ^ 2 ≤ (primorial q + 1) ^ 2 := Nat.pow_le_pow_left hr_le 2
  have hfull_le : fullSieveLevelAtPrime q r ≤ primorial q + (primorial q + 1) ^ 2 := by
    unfold fullSieveLevelAtPrime
    exact Nat.add_le_add_left hr_sq_le (primorial q)
  have hstep : primorial q + (primorial q + 1) ^ 2 < (primorial q + 2) ^ 2 := by
    nlinarith [primorial_pos q]
  have hsq_mon : (primorial q + 2) ^ 2 ≤ (primorial q + q) ^ 2 := by
    exact Nat.pow_le_pow_left (Nat.add_le_add_left hq.two_le (primorial q)) 2
  have hfull_lt : fullSieveLevelAtPrime q r < (primorial q + q) ^ 2 := by
    exact lt_of_le_of_lt hfull_le (lt_of_lt_of_le hstep hsq_mon)
  have hsqrt_lt : Nat.sqrt (fullSieveLevelAtPrime q r) < primorial q + q :=
    (Nat.sqrt_lt').2 hfull_lt
  have hcanon_lt : canonicalSquareSieveLevelAtPrime q r < primorial q + (q + 1) := by
    unfold canonicalSquareSieveLevelAtPrime
    simpa [Nat.add_assoc] using Nat.succ_lt_succ hsqrt_lt
  exact lt_of_lt_of_le hcanon_lt (Nat.add_le_add_left (Nat.succ_le_of_lt hq_lt_m) (primorial q))

/-- Canonical square-root-scale window-sifted target at threshold `q`. -/
def CanonicalSquareWindowSiftedPrimeOffsetExistsAtPrime (q r : Nat) : Prop :=
  WindowSiftedPrimeOffsetExistsAtPrime q r (canonicalSquareSieveLevelAtPrime q r)

/-- If a candidate survives sieving up to an ambient bound that contains
its translate, then the translate is prime. -/
theorem prime_translate_of_siftedPrimeOffsetCandidateAtPrime {q r z m : Nat}
    (hCand : SiftedPrimeOffsetCandidateAtPrime q r z m)
    (hBound : primorial q + m ≤ z) :
    Nat.Prime (primorial q + m) := by
  rcases hCand with ⟨hmPrime, _hq_lt_m, _hm_lt_sq, hSifted⟩
  have htwo_le_sum : 2 ≤ primorial q + m := by
    have hm_le_sum' : m ≤ primorial q + m := by
      calc
        m ≤ m + primorial q := Nat.le_add_right m (primorial q)
        _ = primorial q + m := by ac_rfl
    exact le_trans hmPrime.two_le hm_le_sum'
  have hsum_ne_one : primorial q + m ≠ 1 := ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) htwo_le_sum)
  have hsum_pos : 0 < primorial q + m := by
    exact lt_of_lt_of_le (by decide : 0 < 2) htwo_le_sum
  have hmin_prime : Nat.Prime (Nat.minFac (primorial q + m)) :=
    Nat.minFac_prime hsum_ne_one
  have hmin_dvd : Nat.minFac (primorial q + m) ∣ primorial q + m :=
    Nat.minFac_dvd (primorial q + m)
  have hmin_le_sum : Nat.minFac (primorial q + m) ≤ primorial q + m :=
    Nat.le_of_dvd hsum_pos hmin_dvd
  have hmin_le_z : Nat.minFac (primorial q + m) ≤ z :=
    le_trans hmin_le_sum hBound
  have hmin_eq_sum : Nat.minFac (primorial q + m) = primorial q + m :=
    hSifted (Nat.minFac (primorial q + m)) hmin_prime hmin_le_z hmin_dvd
  exact (Nat.prime_def_minFac).2 ⟨htwo_le_sum, hmin_eq_sum⟩

/-- The windowed sieve formulation is enough for the same primality upgrade. -/
theorem prime_translate_of_windowSiftedPrimeOffsetCandidateAtPrime {q r z m : Nat}
    (hCand : WindowSiftedPrimeOffsetCandidateAtPrime q r z m)
    (hBound : primorial q + m ≤ z) :
    Nat.Prime (primorial q + m) := by
  exact prime_translate_of_siftedPrimeOffsetCandidateAtPrime
    ((siftedPrimeOffsetCandidateAtPrime_iff_windowSiftedPrimeOffsetCandidateAtPrime).2 hCand)
    hBound

/-- If `q# + m` has no prime divisor in the window `q < ℓ ≤ z`, and `z^2`
already dominates `q# + m`, then `q# + m` is prime. -/
theorem prime_translate_of_windowRoughPrimeOffsetCandidateAtPrime {q r z m : Nat}
    (hCand : WindowRoughPrimeOffsetCandidateAtPrime q r z m)
    (hSq : primorial q + m ≤ z ^ 2) :
    Nat.Prime (primorial q + m) := by
  rcases hCand with ⟨hmPrime, hq_lt_m, _hm_lt_sq, hRough⟩
  let n := primorial q + m
  have htwo_le_n : 2 ≤ n := by
    have hm_le_n : m ≤ n := by
      dsimp [n]
      calc
        m ≤ m + primorial q := Nat.le_add_right m (primorial q)
        _ = primorial q + m := by ac_rfl
    exact le_trans hmPrime.two_le hm_le_n
  have hn_ne_one : n ≠ 1 :=
    ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) htwo_le_n)
  have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) htwo_le_n
  by_contra hnPrime
  have hmin_prime : Nat.Prime (Nat.minFac n) := Nat.minFac_prime hn_ne_one
  have hmin_dvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hq_lt_min : q < Nat.minFac n := by
    refine lt_of_not_ge ?_
    intro hmin_le_q
    exact primeOffset_not_dvd_primorial_add_of_prime_le hmPrime hq_lt_m hmin_prime hmin_le_q
      (by simpa [n] using hmin_dvd)
  have hmin_sq_le_n : Nat.minFac n ^ 2 ≤ n := Nat.minFac_sq_le_self hn_pos hnPrime
  have hmin_sq_le_zsq : Nat.minFac n ^ 2 ≤ z ^ 2 := le_trans hmin_sq_le_n (by simpa [n] using hSq)
  have hmin_le_z : Nat.minFac n ≤ z := by
    exact (Nat.pow_le_pow_iff_left (by decide : (2 : Nat) ≠ 0)).1 hmin_sq_le_zsq
  exact (hRough (Nat.minFac n) hmin_prime hq_lt_min hmin_le_z (by simpa [n] using hmin_dvd)).elim

/-- A prime translate automatically satisfies the windowed sifted predicate at
any sieve level. -/
theorem windowSiftedPrimeOffsetCandidateAtPrime_of_primeTranslate {q r z m : Nat}
    (hmPrime : Nat.Prime m)
    (hq_lt_m : q < m)
    (hm_lt_sq : m < r ^ 2)
    (hPrimeSum : Nat.Prime (primorial q + m)) :
    WindowSiftedPrimeOffsetCandidateAtPrime q r z m := by
  refine ⟨hmPrime, hq_lt_m, hm_lt_sq, ?_⟩
  intro ℓ hℓPrime _hq_lt_ℓ _hℓ_le_z hℓ_dvd_sum
  rcases (Nat.dvd_prime hPrimeSum).1 hℓ_dvd_sum with hℓ_eq_one | hℓ_eq_sum
  · exact False.elim (hℓPrime.ne_one hℓ_eq_one)
  · exact hℓ_eq_sum

/-- A sieve statement at level `z` upgrades to the prime-offset formulation
once `z` dominates the whole Route 2 interval endpoint. -/
theorem primeOffsetPrimeExistsAtPrime_of_siftedPrimeOffsetExistsAtPrime {q r z : Nat}
    (hExists : SiftedPrimeOffsetExistsAtPrime q r z)
    (hLevel : fullSieveLevelAtPrime q r ≤ z) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  rcases hExists with ⟨m, hmPrime, hq_lt_m, hm_lt_sq, hSifted⟩
  refine ⟨m, hmPrime, hq_lt_m, hm_lt_sq, ?_⟩
  apply prime_translate_of_siftedPrimeOffsetCandidateAtPrime
  · exact ⟨hmPrime, hq_lt_m, hm_lt_sq, hSifted⟩
  · have hsum_lt_level : primorial q + m < fullSieveLevelAtPrime q r := by
      exact Nat.add_lt_add_left hm_lt_sq (primorial q)
    exact le_trans (Nat.le_of_lt hsum_lt_level) hLevel

/-- The windowed sieve existence statement upgrades in the same way. -/
theorem primeOffsetPrimeExistsAtPrime_of_windowSiftedPrimeOffsetExistsAtPrime {q r z : Nat}
    (hExists : WindowSiftedPrimeOffsetExistsAtPrime q r z)
    (hLevel : fullSieveLevelAtPrime q r ≤ z) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  rcases hExists with ⟨m, hmPrime, hq_lt_m, hm_lt_sq, hWindow⟩
  refine ⟨m, hmPrime, hq_lt_m, hm_lt_sq, ?_⟩
  apply prime_translate_of_windowSiftedPrimeOffsetCandidateAtPrime
  · exact ⟨hmPrime, hq_lt_m, hm_lt_sq, hWindow⟩
  · have hsum_lt_level : primorial q + m < fullSieveLevelAtPrime q r := by
      exact Nat.add_lt_add_left hm_lt_sq (primorial q)
    exact le_trans (Nat.le_of_lt hsum_lt_level) hLevel

/-- A window-rough existence statement upgrades once the square of the sieve
level dominates the whole Route 2 interval endpoint. -/
theorem primeOffsetPrimeExistsAtPrime_of_windowRoughPrimeOffsetExistsAtPrime {q r z : Nat}
    (hExists : WindowRoughPrimeOffsetExistsAtPrime q r z)
    (hSq : fullSieveLevelAtPrime q r ≤ z ^ 2) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  rcases hExists with ⟨m, hmPrime, hq_lt_m, hm_lt_sq, hRough⟩
  refine ⟨m, hmPrime, hq_lt_m, hm_lt_sq, ?_⟩
  apply prime_translate_of_windowRoughPrimeOffsetCandidateAtPrime
  · exact ⟨hmPrime, hq_lt_m, hm_lt_sq, hRough⟩
  · have hsum_lt_level : primorial q + m < fullSieveLevelAtPrime q r := by
      exact Nat.add_lt_add_left hm_lt_sq (primorial q)
    exact le_trans (Nat.le_of_lt hsum_lt_level) hSq

/-- Specialized full-sieve target at threshold `q`. -/
def FullSiftedPrimeOffsetExistsAtPrime (q r : Nat) : Prop :=
  SiftedPrimeOffsetExistsAtPrime q r (fullSieveLevelAtPrime q r)

/-- Specialized full window-sieve target at threshold `q`. -/
def FullWindowSiftedPrimeOffsetExistsAtPrime (q r : Nat) : Prop :=
  WindowSiftedPrimeOffsetExistsAtPrime q r (fullSieveLevelAtPrime q r)

/-- Specialized window-rough target at threshold `q`. -/
def FullWindowRoughPrimeOffsetExistsAtPrime (q r z : Nat) : Prop :=
  WindowRoughPrimeOffsetExistsAtPrime q r z ∧ fullSieveLevelAtPrime q r ≤ z ^ 2

/-- Specialized canonical square-root-scale window-rough target at threshold `q`. -/
def CanonicalSquareWindowRoughPrimeOffsetExistsAtPrime (q r : Nat) : Prop :=
  WindowRoughPrimeOffsetExistsAtPrime q r (canonicalSquareSieveLevelAtPrime q r)

theorem siftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime {q r z : Nat}
    (hExists : PrimeOffsetPrimeExistsAtPrime q r) :
    SiftedPrimeOffsetExistsAtPrime q r z := by
  rcases hExists with ⟨m, hmPrime, hq_lt_m, hm_lt_sq, hPrimeSum⟩
  exact (siftedPrimeOffsetExistsAtPrime_iff_windowSiftedPrimeOffsetExistsAtPrime).2
    ⟨m, windowSiftedPrimeOffsetCandidateAtPrime_of_primeTranslate
      hmPrime hq_lt_m hm_lt_sq hPrimeSum⟩

theorem windowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime {q r z : Nat}
    (hExists : PrimeOffsetPrimeExistsAtPrime q r) :
    WindowSiftedPrimeOffsetExistsAtPrime q r z := by
  rcases hExists with ⟨m, hmPrime, hq_lt_m, hm_lt_sq, hPrimeSum⟩
  exact ⟨m, windowSiftedPrimeOffsetCandidateAtPrime_of_primeTranslate
    hmPrime hq_lt_m hm_lt_sq hPrimeSum⟩

theorem fullSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime {q r : Nat}
    (hExists : PrimeOffsetPrimeExistsAtPrime q r) :
    FullSiftedPrimeOffsetExistsAtPrime q r :=
  siftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime hExists

theorem fullWindowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime {q r : Nat}
    (hExists : PrimeOffsetPrimeExistsAtPrime q r) :
    FullWindowSiftedPrimeOffsetExistsAtPrime q r :=
  windowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime hExists

theorem canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime
    {q r : Nat}
    (hExists : PrimeOffsetPrimeExistsAtPrime q r) :
    CanonicalSquareWindowSiftedPrimeOffsetExistsAtPrime q r :=
  windowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime hExists

theorem windowRoughPrimeOffsetCandidateAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetCandidateAtPrime
    {q r m : Nat}
    (hqr : ConsecutivePrimes q r)
    (hCand : WindowSiftedPrimeOffsetCandidateAtPrime q r
      (canonicalSquareSieveLevelAtPrime q r) m) :
    WindowRoughPrimeOffsetCandidateAtPrime q r
      (canonicalSquareSieveLevelAtPrime q r) m := by
  rcases hCand with ⟨hmPrime, hq_lt_m, hm_lt_sq, hSifted⟩
  exact windowRoughPrimeOffsetCandidateAtPrime_of_windowSiftedPrimeOffsetCandidateAtPrime
    ⟨hmPrime, hq_lt_m, hm_lt_sq, hSifted⟩
    (canonicalSquareSieveLevelAtPrime_lt_translate_of_consecutivePrimes hqr hq_lt_m)

theorem canonicalSquareWindowRoughPrimeOffsetExistsAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime
    {q r : Nat}
    (hqr : ConsecutivePrimes q r)
    (hExists : CanonicalSquareWindowSiftedPrimeOffsetExistsAtPrime q r) :
    CanonicalSquareWindowRoughPrimeOffsetExistsAtPrime q r := by
  rcases hExists with ⟨m, hm⟩
  exact ⟨m,
    windowRoughPrimeOffsetCandidateAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetCandidateAtPrime
      hqr hm⟩

theorem fullSiftedPrimeOffsetExistsAtPrime_iff_fullWindowSiftedPrimeOffsetExistsAtPrime
    {q r : Nat} :
    FullSiftedPrimeOffsetExistsAtPrime q r ↔
      FullWindowSiftedPrimeOffsetExistsAtPrime q r :=
  siftedPrimeOffsetExistsAtPrime_iff_windowSiftedPrimeOffsetExistsAtPrime

/-- The full-sieve target implies the prime-offset formulation. -/
theorem primeOffsetPrimeExistsAtPrime_of_fullSiftedPrimeOffsetExistsAtPrime
    {q r : Nat}
    (hExists : FullSiftedPrimeOffsetExistsAtPrime q r) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  exact primeOffsetPrimeExistsAtPrime_of_siftedPrimeOffsetExistsAtPrime hExists (le_rfl)

/-- The full window-sieve target implies the prime-offset formulation. -/
theorem primeOffsetPrimeExistsAtPrime_of_fullWindowSiftedPrimeOffsetExistsAtPrime
    {q r : Nat}
    (hExists : FullWindowSiftedPrimeOffsetExistsAtPrime q r) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  exact primeOffsetPrimeExistsAtPrime_of_windowSiftedPrimeOffsetExistsAtPrime hExists (le_rfl)

/-- The square-bounded window-rough target implies the prime-offset formulation. -/
theorem primeOffsetPrimeExistsAtPrime_of_fullWindowRoughPrimeOffsetExistsAtPrime
    {q r z : Nat}
    (hExists : FullWindowRoughPrimeOffsetExistsAtPrime q r z) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  exact primeOffsetPrimeExistsAtPrime_of_windowRoughPrimeOffsetExistsAtPrime hExists.1 hExists.2

/-- The canonical square-root-scale window-rough target implies the prime-offset formulation. -/
theorem primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowRoughPrimeOffsetExistsAtPrime
    {q r : Nat}
    (hExists : CanonicalSquareWindowRoughPrimeOffsetExistsAtPrime q r) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  exact primeOffsetPrimeExistsAtPrime_of_windowRoughPrimeOffsetExistsAtPrime hExists
    fullSieveLevelAtPrime_le_canonicalSquareSieveLevelAtPrime_sq

/-- The canonical square-root-scale window-sifted target also implies the prime-offset formulation. -/
theorem primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime
    {q r : Nat}
    (hqr : ConsecutivePrimes q r)
    (hExists : CanonicalSquareWindowSiftedPrimeOffsetExistsAtPrime q r) :
    PrimeOffsetPrimeExistsAtPrime q r := by
  exact primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowRoughPrimeOffsetExistsAtPrime
    (canonicalSquareWindowRoughPrimeOffsetExistsAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime
      hqr hExists)

end Fortune
