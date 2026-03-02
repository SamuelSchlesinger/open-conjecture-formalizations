import Fortune.Defs
import Fortune.Literature
import Fortune.Bridge
import Fortune.Reduction
import Fortune.ReductionBound
import Fortune.Congruence
import Fortune.Profile
import Fortune.LowerInterval
import Fortune.CertifiedRange
import Mathlib.NumberTheory.Primorial

namespace Fortune

/-!
# Formalization Progress (Fortune)

This module records named route-level statements and their current formal status.
The only unresolved route-level hypothesis is the primorial upper-interval prime
existence condition used to derive the Route 2.A reduction bound.
-/

/-- Route 1.A: identify indexed and threshold primorials. -/
def Route1PrimorialBridge : Prop :=
  ∀ n : Nat, 1 ≤ n → nthPrimorial n = primorial (lastIncludedPrime n)

/-- Route 1.B: transfer least-offset statements between indexed and threshold models. -/
def Route1LeastOffsetBridge : Prop :=
  ∀ n m : Nat, 1 ≤ n →
    (IsLeastFortunateOffset n m ↔ IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m)

/-- Route 1.C: for each `n`, obtain a consecutive-prime witness at `lastIncludedPrime n`. -/
def Route1NextPrimeWitness : Prop :=
  ∀ n : Nat, 1 ≤ n →
    ∃ r : Nat, ConsecutivePrimes (lastIncludedPrime n) r

theorem route1_primorialBridge :
    Route1PrimorialBridge := by
  intro n hn
  exact bridge_nthPrimorial_eq_primorial_lastIncludedPrime n hn

theorem route1_leastOffsetBridge :
    Route1LeastOffsetBridge := by
  intro n m hn
  exact bridge_leastOffset_indexed_to_threshold n m hn

theorem route1_nextPrimeWitness :
    Route1NextPrimeWitness := by
  intro n hn
  exact bridge_exists_nextPrime_at_lastIncluded n hn

/-- Route 2.A target: quantitative reduction bound. -/
def Route2ReductionBound : Prop :=
  ∀ n m r : Nat, 1 ≤ n →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

/-- Open Route 2 interval-existence hypothesis:
for each `n` and consecutive-prime witness `r` at `lastIncludedPrime n`,
there exists a prime in `(q# + 1, q# + r^2)`. -/
def Route2IntervalPrimeExistence : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    ∃ p : Nat, Nat.Prime p ∧
      primorial (lastIncludedPrime n) + 1 < p ∧
      p < primorial (lastIncludedPrime n) + r ^ 2

theorem route2_reductionBound_of_intervalPrimeExistence :
    Route2IntervalPrimeExistence → Route2ReductionBound := by
  intro hInterval
  exact reduction_bound_of_intervalPrimeExists_at_lastIncluded hInterval

/-- Route 2.B reduction theorem. -/
def Route2BoundImpliesFortune : Prop :=
  Route2ReductionBound → FortuneConjecture

theorem route2_boundImpliesFortune :
    Route2BoundImpliesFortune := by
  intro hBound
  exact reduction_bound_implies_fortune hBound

/-- Route 3 congruence-obstruction profile. -/
def Route3CongruenceObstructions : Prop :=
  ∀ n m i : Nat, 1 ≤ n →
    IsLeastFortunateOffset n m →
    i < n →
    ¬ m ≡ 0 [MOD nthPrime i]

theorem route3_congruenceObstructions :
    Route3CongruenceObstructions := by
  intro n m i hn hLeast hi
  exact leastFortunateOffset_not_modEq_zero_nthPrime hLeast hi

/-- Route 4 prime-divisor profile strengthening. -/
def Route4PrimeDivisorProfile : Prop :=
  ∀ n m p : Nat, 1 ≤ n →
    IsLeastFortunateOffset n m →
    Nat.Prime p →
    p ∣ m →
    lastIncludedPrime n < p

theorem route4_primeDivisorProfile :
    Route4PrimeDivisorProfile := by
  intro n m p hn hLeast hp hpdvd
  exact prime_divisor_gt_lastIncludedPrime_of_leastOffset hn hLeast hp hpdvd

/-- Route 5 tightened lower-interval theorem. -/
def Route5LowerIntervalTightening : Prop :=
  ∀ s q p : Nat,
    ConsecutivePrimes s q →
    Nat.Prime p →
    q < primorial q - s ^ 2 →
    primorial q - s ^ 2 < p →
    p < primorial q - 1 →
    Nat.Prime (primorial q - p)

theorem route5_lowerIntervalTightening :
    Route5LowerIntervalTightening := by
  intro s q p hsq hp hq_left hlow hhigh
  exact prime_primorial_sub_of_interval_tight hsq hp hq_left hlow hhigh

/-- Route 6 current certified range extension. -/
def Route6CertifiedRange : Prop :=
  ∀ n : Nat, 1 ≤ n → n ≤ 5 →
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m

theorem route6_certifiedRange :
    Route6CertifiedRange := by
  intro n hn1 hn5
  exact hasPrimeLeastFortunateOffset_one_to_five hn1 hn5

end Fortune
