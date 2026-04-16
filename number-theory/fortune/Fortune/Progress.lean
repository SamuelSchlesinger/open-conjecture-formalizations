import Fortune.Defs
import Fortune.Literature
import Fortune.Bridge
import Fortune.Reduction
import Fortune.ReductionBound
import Fortune.IntervalExistence
import Fortune.Sieve
import Fortune.IntervalExistenceSmall
import Fortune.Congruence
import Fortune.Profile
import Fortune.LowerInterval
import Fortune.CertifiedRange
import Mathlib.NumberTheory.Primorial

namespace Fortune

/-!
# Formalization Progress (Fortune)

This module records named route-level statements and their current formal status.
The unresolved route-level hypotheses are the primorial upper-interval prime
existence condition and its stronger prime-offset variant.
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

/-- Stronger Route 2 research target:
there exists a prime offset `m` with `q < m < r^2` and `q# + m` prime,
where `q = lastIncludedPrime n`. -/
def Route2PrimeOffsetPrimeExistence : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    PrimeOffsetPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_intervalPrimeExistence_of_primeOffsetPrimeExistence :
    Route2PrimeOffsetPrimeExistence → Route2IntervalPrimeExistence := by
  intro hPrimeOffset n r hn hqr
  exact intervalPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime
    (hPrimeOffset n r hn hqr)

theorem route2_primeOffsetPrimeExistence_of_intervalPrimeExistence :
    Route2IntervalPrimeExistence → Route2PrimeOffsetPrimeExistence := by
  intro hInterval n r hn hqr
  exact primeOffsetPrimeExistsAtPrime_of_intervalPrimeExistsAtPrime hqr
    (hInterval n r hn hqr)

theorem route2_intervalPrimeExistence_iff_primeOffsetPrimeExistence :
    Route2IntervalPrimeExistence ↔ Route2PrimeOffsetPrimeExistence := by
  constructor
  · exact route2_primeOffsetPrimeExistence_of_intervalPrimeExistence
  · exact route2_intervalPrimeExistence_of_primeOffsetPrimeExistence

theorem route2_reductionBound_of_intervalPrimeExistence :
    Route2IntervalPrimeExistence → Route2ReductionBound := by
  intro hInterval
  exact reduction_bound_of_intervalPrimeExists_at_lastIncluded hInterval

theorem route2_reductionBound_of_primeOffsetPrimeExistence :
    Route2PrimeOffsetPrimeExistence → Route2ReductionBound := by
  intro hPrimeOffset
  exact route2_reductionBound_of_intervalPrimeExistence
    (route2_intervalPrimeExistence_of_primeOffsetPrimeExistence hPrimeOffset)

/-- Route 2 sieve-stage statement at a variable sieve level `Z q r`. -/
def Route2SieveLowerBound (Z : Nat → Nat → Nat) : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    SiftedPrimeOffsetExistsAtPrime (lastIncludedPrime n) r (Z (lastIncludedPrime n) r)

/-- Windowed Route 2 sieve-stage statement:
only primes `ℓ` with `q < ℓ ≤ Z q r` are checked. -/
def Route2WindowSieveLowerBound (Z : Nat → Nat → Nat) : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    WindowSiftedPrimeOffsetExistsAtPrime (lastIncludedPrime n) r (Z (lastIncludedPrime n) r)

/-- Windowed rough Route 2 sieve-stage statement:
no prime divisor occurs in the window `q < ℓ ≤ Z q r`. -/
def Route2WindowRoughLowerBound (Z : Nat → Nat → Nat) : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    WindowRoughPrimeOffsetExistsAtPrime (lastIncludedPrime n) r (Z (lastIncludedPrime n) r)

/-- Route 2 parity/primality upgrade at a variable sieve level `Z q r`. -/
def Route2ParityUpgrade (Z : Nat → Nat → Nat) : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    SiftedPrimeOffsetExistsAtPrime (lastIncludedPrime n) r (Z (lastIncludedPrime n) r) →
    PrimeOffsetPrimeExistsAtPrime (lastIncludedPrime n) r

/-- Windowed Route 2 parity/primality upgrade. -/
def Route2WindowParityUpgrade (Z : Nat → Nat → Nat) : Prop :=
  ∀ n r : Nat, 1 ≤ n →
    ConsecutivePrimes (lastIncludedPrime n) r →
    WindowSiftedPrimeOffsetExistsAtPrime (lastIncludedPrime n) r (Z (lastIncludedPrime n) r) →
    PrimeOffsetPrimeExistsAtPrime (lastIncludedPrime n) r

/-- Square-bound hypothesis for a sieve level `Z q r`. -/
def Route2SquareSieveLevel (Z : Nat → Nat → Nat) : Prop :=
  ∀ q r : Nat, fullSieveLevelAtPrime q r ≤ Z q r ^ 2

theorem route2_squareSieveLevel_canonical :
    Route2SquareSieveLevel canonicalSquareSieveLevelAtPrime := by
  intro q r
  exact fullSieveLevelAtPrime_le_canonicalSquareSieveLevelAtPrime_sq

/-- The natural full-sieve level attached to the Route 2 interval. -/
def Route2FullSieveLevel (q r : Nat) : Nat :=
  fullSieveLevelAtPrime q r

/-- The sieve-stage target at the full interval endpoint. -/
def Route2FullSiftedPrimeOffsetExistence : Prop :=
  Route2SieveLowerBound Route2FullSieveLevel

/-- The windowed sieve-stage target at the full interval endpoint. -/
def Route2FullWindowSiftedPrimeOffsetExistence : Prop :=
  Route2WindowSieveLowerBound Route2FullSieveLevel

/-- Canonical square-root-scale window-sifted target. -/
def Route2CanonicalSquareWindowSiftedExistence : Prop :=
  Route2WindowSieveLowerBound canonicalSquareSieveLevelAtPrime

/-- Canonical square-root-scale window-rough target. -/
def Route2CanonicalSquareWindowRoughExistence : Prop :=
  Route2WindowRoughLowerBound canonicalSquareSieveLevelAtPrime

theorem route2SieveLowerBound_iff_route2WindowSieveLowerBound
    {Z : Nat → Nat → Nat} :
    Route2SieveLowerBound Z ↔ Route2WindowSieveLowerBound Z := by
  constructor
  · intro h n r hn hqr
    exact (siftedPrimeOffsetExistsAtPrime_iff_windowSiftedPrimeOffsetExistsAtPrime).1
      (h n r hn hqr)
  · intro h n r hn hqr
    exact (siftedPrimeOffsetExistsAtPrime_iff_windowSiftedPrimeOffsetExistsAtPrime).2
      (h n r hn hqr)

theorem route2FullSiftedPrimeOffsetExistence_iff_route2FullWindowSiftedPrimeOffsetExistence :
    Route2FullSiftedPrimeOffsetExistence ↔ Route2FullWindowSiftedPrimeOffsetExistence :=
  route2SieveLowerBound_iff_route2WindowSieveLowerBound

theorem route2_primeOffsetPrimeExistence_of_sieveLowerBound_and_parityUpgrade
    {Z : Nat → Nat → Nat}
    (hSieve : Route2SieveLowerBound Z)
    (hParity : Route2ParityUpgrade Z) :
    Route2PrimeOffsetPrimeExistence := by
  intro n r hn hqr
  exact hParity n r hn hqr (hSieve n r hn hqr)

theorem route2_primeOffsetPrimeExistence_of_windowSieveLowerBound_and_parityUpgrade
    {Z : Nat → Nat → Nat}
    (hSieve : Route2WindowSieveLowerBound Z)
    (hParity : Route2WindowParityUpgrade Z) :
    Route2PrimeOffsetPrimeExistence := by
  intro n r hn hqr
  exact hParity n r hn hqr (hSieve n r hn hqr)

theorem route2_windowParityUpgrade_of_squareSieveLevel
    {Z : Nat → Nat → Nat}
    (hSq : Route2SquareSieveLevel Z) :
    ∀ n r : Nat, 1 ≤ n →
      ConsecutivePrimes (lastIncludedPrime n) r →
      WindowRoughPrimeOffsetExistsAtPrime (lastIncludedPrime n) r (Z (lastIncludedPrime n) r) →
      PrimeOffsetPrimeExistsAtPrime (lastIncludedPrime n) r := by
  intro n r hn hqr hRough
  exact primeOffsetPrimeExistsAtPrime_of_windowRoughPrimeOffsetExistsAtPrime hRough
    (hSq (lastIncludedPrime n) r)

theorem route2_primeOffsetPrimeExistence_of_windowRoughLowerBound_and_squareSieveLevel
    {Z : Nat → Nat → Nat}
    (hRough : Route2WindowRoughLowerBound Z)
    (hSq : Route2SquareSieveLevel Z) :
    Route2PrimeOffsetPrimeExistence := by
  intro n r hn hqr
  exact route2_windowParityUpgrade_of_squareSieveLevel hSq n r hn hqr (hRough n r hn hqr)

theorem route2_primeOffsetPrimeExistence_of_canonicalSquareWindowRoughExistence :
    Route2CanonicalSquareWindowRoughExistence → Route2PrimeOffsetPrimeExistence := by
  intro hCanon
  exact route2_primeOffsetPrimeExistence_of_windowRoughLowerBound_and_squareSieveLevel
    hCanon route2_squareSieveLevel_canonical

theorem route2_canonicalSquareWindowSiftedExistence_of_primeOffsetPrimeExistence :
    Route2PrimeOffsetPrimeExistence → Route2CanonicalSquareWindowSiftedExistence := by
  intro hPrimeOffset n r hn hqr
  exact canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime
    (hPrimeOffset n r hn hqr)

theorem route2_windowParityUpgrade_canonicalSquare :
    Route2WindowParityUpgrade canonicalSquareSieveLevelAtPrime := by
  intro n r hn hqr hSifted
  exact primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime
    hqr hSifted

theorem route2_canonicalSquareWindowRoughExistence_of_canonicalSquareWindowSiftedExistence :
    Route2CanonicalSquareWindowSiftedExistence → Route2CanonicalSquareWindowRoughExistence := by
  intro hCanon n r hn hqr
  exact
    canonicalSquareWindowRoughPrimeOffsetExistsAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime
      hqr (hCanon n r hn hqr)

theorem route2_primeOffsetPrimeExistence_of_canonicalSquareWindowSiftedExistence :
    Route2CanonicalSquareWindowSiftedExistence → Route2PrimeOffsetPrimeExistence := by
  intro hCanon
  exact route2_primeOffsetPrimeExistence_of_windowSieveLowerBound_and_parityUpgrade
    hCanon route2_windowParityUpgrade_canonicalSquare

theorem route2_parityUpgrade_fullSieve :
    Route2ParityUpgrade Route2FullSieveLevel := by
  intro n r hn hqr hSifted
  exact primeOffsetPrimeExistsAtPrime_of_fullSiftedPrimeOffsetExistsAtPrime hSifted

theorem route2_windowParityUpgrade_fullSieve :
    Route2WindowParityUpgrade Route2FullSieveLevel := by
  intro n r hn hqr hSifted
  exact primeOffsetPrimeExistsAtPrime_of_fullWindowSiftedPrimeOffsetExistsAtPrime hSifted

theorem route2_primeOffsetPrimeExistence_of_fullSiftedPrimeOffsetExistence :
    Route2FullSiftedPrimeOffsetExistence → Route2PrimeOffsetPrimeExistence := by
  intro hFull
  exact route2_primeOffsetPrimeExistence_of_sieveLowerBound_and_parityUpgrade
    hFull route2_parityUpgrade_fullSieve

theorem route2_primeOffsetPrimeExistence_of_fullWindowSiftedPrimeOffsetExistence :
    Route2FullWindowSiftedPrimeOffsetExistence → Route2PrimeOffsetPrimeExistence := by
  intro hFull
  exact route2_primeOffsetPrimeExistence_of_windowSieveLowerBound_and_parityUpgrade
    hFull route2_windowParityUpgrade_fullSieve

theorem route2_reductionBound_of_fullSiftedPrimeOffsetExistence :
    Route2FullSiftedPrimeOffsetExistence → Route2ReductionBound := by
  intro hFull
  exact route2_reductionBound_of_primeOffsetPrimeExistence
    (route2_primeOffsetPrimeExistence_of_fullSiftedPrimeOffsetExistence hFull)

theorem route2_reductionBound_of_fullWindowSiftedPrimeOffsetExistence :
    Route2FullWindowSiftedPrimeOffsetExistence → Route2ReductionBound := by
  intro hFull
  exact route2_reductionBound_of_primeOffsetPrimeExistence
    (route2_primeOffsetPrimeExistence_of_fullWindowSiftedPrimeOffsetExistence hFull)

theorem route2_reductionBound_of_windowRoughLowerBound_and_squareSieveLevel
    {Z : Nat → Nat → Nat}
    (hRough : Route2WindowRoughLowerBound Z)
    (hSq : Route2SquareSieveLevel Z) :
    Route2ReductionBound := by
  exact route2_reductionBound_of_primeOffsetPrimeExistence
    (route2_primeOffsetPrimeExistence_of_windowRoughLowerBound_and_squareSieveLevel hRough hSq)

theorem route2_reductionBound_of_canonicalSquareWindowRoughExistence :
    Route2CanonicalSquareWindowRoughExistence → Route2ReductionBound := by
  intro hCanon
  exact route2_reductionBound_of_primeOffsetPrimeExistence
    (route2_primeOffsetPrimeExistence_of_canonicalSquareWindowRoughExistence hCanon)

theorem route2_reductionBound_of_canonicalSquareWindowSiftedExistence :
    Route2CanonicalSquareWindowSiftedExistence → Route2ReductionBound := by
  intro hCanon
  exact route2_reductionBound_of_primeOffsetPrimeExistence
    (route2_primeOffsetPrimeExistence_of_canonicalSquareWindowSiftedExistence hCanon)

/-- Converse Route 2 direction: the reduction bound yields interval-prime existence. -/
theorem route2_intervalPrimeExistence_of_reductionBound :
    Route2ReductionBound → Route2IntervalPrimeExistence := by
  intro hBound
  exact intervalPrimeExistence_of_reductionBound hBound

/-- Route 2 equivalence between interval-prime existence and reduction bound. -/
theorem route2_intervalPrimeExistence_iff_reductionBound :
    Route2IntervalPrimeExistence ↔ Route2ReductionBound :=
  intervalPrimeExistence_iff_reductionBound

/-- Finite verified interval-prime existence for `1 ≤ n ≤ 5`. -/
def Route2IntervalPrimeExistenceOneToFive : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 5 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_intervalPrimeExistence_one_to_five_progress :
    Route2IntervalPrimeExistenceOneToFive := by
  intro n r hn1 hn5 hqr
  exact Fortune.route2_intervalPrimeExistence_one_to_five hn1 hn5 hqr

def Route2ReductionBoundOneToFive : Prop :=
  ∀ n m r : Nat, 1 ≤ n → n ≤ 5 →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

theorem route2_reductionBound_one_to_five_progress :
    Route2ReductionBoundOneToFive := by
  intro n m r hn1 hn5 hLeast hqr
  exact Fortune.route2_reductionBound_one_to_five hn1 hn5 hLeast hqr

def Route2IntervalPrimeExistenceOneToSix : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 6 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_intervalPrimeExistence_one_to_six_progress :
    Route2IntervalPrimeExistenceOneToSix := by
  intro n r hn1 hn6 hqr
  exact Fortune.route2_intervalPrimeExistence_one_to_six hn1 hn6 hqr

def Route2ReductionBoundOneToSix : Prop :=
  ∀ n m r : Nat, 1 ≤ n → n ≤ 6 →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

theorem route2_reductionBound_one_to_six_progress :
    Route2ReductionBoundOneToSix := by
  intro n m r hn1 hn6 hLeast hqr
  exact Fortune.route2_reductionBound_one_to_six hn1 hn6 hLeast hqr

def Route2IntervalPrimeExistenceOneToTwelve : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 12 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_intervalPrimeExistence_one_to_twelve_progress :
    Route2IntervalPrimeExistenceOneToTwelve := by
  intro n r hn1 hn12 hqr
  exact Fortune.route2_intervalPrimeExistence_one_to_twelve hn1 hn12 hqr

def Route2ReductionBoundOneToTwelve : Prop :=
  ∀ n m r : Nat, 1 ≤ n → n ≤ 12 →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

theorem route2_reductionBound_one_to_twelve_progress :
    Route2ReductionBoundOneToTwelve := by
  intro n m r hn1 hn12 hLeast hqr
  exact Fortune.route2_reductionBound_one_to_twelve hn1 hn12 hLeast hqr

def Route2IntervalPrimeExistenceOneToFifteen : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 15 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_intervalPrimeExistence_one_to_fifteen_progress :
    Route2IntervalPrimeExistenceOneToFifteen := by
  intro n r hn1 hn15 hqr
  exact Fortune.route2_intervalPrimeExistence_one_to_fifteen hn1 hn15 hqr

def Route2ReductionBoundOneToFifteen : Prop :=
  ∀ n m r : Nat, 1 ≤ n → n ≤ 15 →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

theorem route2_reductionBound_one_to_fifteen_progress :
    Route2ReductionBoundOneToFifteen := by
  intro n m r hn1 hn15 hLeast hqr
  exact Fortune.route2_reductionBound_one_to_fifteen hn1 hn15 hLeast hqr

def Route2IntervalPrimeExistenceOneToSixteen : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 16 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_intervalPrimeExistence_one_to_sixteen_progress :
    Route2IntervalPrimeExistenceOneToSixteen := by
  intro n r hn1 hn16 hqr
  exact Fortune.route2_intervalPrimeExistence_one_to_sixteen hn1 hn16 hqr

def Route2ReductionBoundOneToSixteen : Prop :=
  ∀ n m r : Nat, 1 ≤ n → n ≤ 16 →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

theorem route2_reductionBound_one_to_sixteen_progress :
    Route2ReductionBoundOneToSixteen := by
  intro n m r hn1 hn16 hLeast hqr
  exact Fortune.route2_reductionBound_one_to_sixteen hn1 hn16 hLeast hqr

def Route2IntervalPrimeExistenceOneToSeventeen : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 17 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    IntervalPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_intervalPrimeExistence_one_to_seventeen_progress :
    Route2IntervalPrimeExistenceOneToSeventeen := by
  intro n r hn1 hn17 hqr
  exact Fortune.route2_intervalPrimeExistence_one_to_seventeen hn1 hn17 hqr

def Route2ReductionBoundOneToSeventeen : Prop :=
  ∀ n m r : Nat, 1 ≤ n → n ≤ 17 →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

theorem route2_reductionBound_one_to_seventeen_progress :
    Route2ReductionBoundOneToSeventeen := by
  intro n m r hn1 hn17 hLeast hqr
  exact Fortune.route2_reductionBound_one_to_seventeen hn1 hn17 hLeast hqr

def Route2PrimeOffsetPrimeExistenceOneToSeventeen : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 17 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    PrimeOffsetPrimeExistsAtPrime (lastIncludedPrime n) r

theorem route2_primeOffsetPrimeExistence_one_to_seventeen_progress :
    Route2PrimeOffsetPrimeExistenceOneToSeventeen := by
  intro n r hn1 hn17 hqr
  exact primeOffsetPrimeExistsAtPrime_of_intervalPrimeExistsAtPrime hqr
    (Fortune.route2_intervalPrimeExistence_one_to_seventeen hn1 hn17 hqr)

def Route2CanonicalSquareWindowSiftedExistenceOneToSeventeen : Prop :=
  ∀ n r : Nat, 1 ≤ n → n ≤ 17 →
    ConsecutivePrimes (lastIncludedPrime n) r →
    CanonicalSquareWindowSiftedPrimeOffsetExistsAtPrime (lastIncludedPrime n) r

theorem route2_canonicalSquareWindowSiftedExistence_one_to_seventeen_progress :
    Route2CanonicalSquareWindowSiftedExistenceOneToSeventeen := by
  intro n r hn1 hn17 hqr
  exact canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime
    (route2_primeOffsetPrimeExistence_one_to_seventeen_progress n r hn1 hn17 hqr)

/-- Route 2.B reduction theorem. -/
def Route2BoundImpliesFortune : Prop :=
  Route2ReductionBound → FortuneConjecture

theorem route2_boundImpliesFortune :
    Route2BoundImpliesFortune := by
  intro hBound
  exact reduction_bound_implies_fortune hBound

theorem route2_fortune_of_primeOffsetPrimeExistence :
    Route2PrimeOffsetPrimeExistence → FortuneConjecture := by
  intro hPrimeOffset
  exact route2_boundImpliesFortune
    (route2_reductionBound_of_primeOffsetPrimeExistence hPrimeOffset)

theorem route2_fortune_of_fullSiftedPrimeOffsetExistence :
    Route2FullSiftedPrimeOffsetExistence → FortuneConjecture := by
  intro hFull
  exact route2_boundImpliesFortune
    (route2_reductionBound_of_fullSiftedPrimeOffsetExistence hFull)

theorem route2_fortune_of_fullWindowSiftedPrimeOffsetExistence :
    Route2FullWindowSiftedPrimeOffsetExistence → FortuneConjecture := by
  intro hFull
  exact route2_boundImpliesFortune
    (route2_reductionBound_of_fullWindowSiftedPrimeOffsetExistence hFull)

theorem route2_fortune_of_windowRoughLowerBound_and_squareSieveLevel
    {Z : Nat → Nat → Nat}
    (hRough : Route2WindowRoughLowerBound Z)
    (hSq : Route2SquareSieveLevel Z) :
    FortuneConjecture := by
  exact route2_boundImpliesFortune
    (route2_reductionBound_of_windowRoughLowerBound_and_squareSieveLevel hRough hSq)

theorem route2_fortune_of_canonicalSquareWindowRoughExistence :
    Route2CanonicalSquareWindowRoughExistence → FortuneConjecture := by
  intro hCanon
  exact route2_boundImpliesFortune
    (route2_reductionBound_of_canonicalSquareWindowRoughExistence hCanon)

theorem route2_fortune_of_canonicalSquareWindowSiftedExistence :
    Route2CanonicalSquareWindowSiftedExistence → FortuneConjecture := by
  intro hCanon
  exact route2_boundImpliesFortune
    (route2_reductionBound_of_canonicalSquareWindowSiftedExistence hCanon)

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
  ∀ n m : Nat, 1 ≤ n →
    IsLeastFortunateOffset n m →
    Nat.Coprime m (primorial (lastIncludedPrime n)) ∧
      (∀ d : Nat, 1 < d → d ∣ m → lastIncludedPrime n < d)

theorem route4_primeDivisorProfile :
    Route4PrimeDivisorProfile := by
  intro n m hn hLeast
  refine ⟨leastOffset_coprime_primorial_lastIncludedPrime hn hLeast, ?_⟩
  intro d hd_gt_one hddvd
  exact divisor_gt_lastIncludedPrime_of_leastOffset hn hLeast hd_gt_one hddvd

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
  ∀ n : Nat, 1 ≤ n → n ≤ 17 →
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m

theorem route6_certifiedRange :
    Route6CertifiedRange := by
  intro n hn1 hn17
  exact hasPrimeLeastFortunateOffset_one_to_seventeen hn1 hn17

end Fortune
