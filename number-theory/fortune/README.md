# Fortune's Conjecture

A Lean 4 formalization scaffold for Fortune's conjecture.

Research notes live in [`research/`](./research/index.md). The current strategy
note is the stronger
[`prime-offset formulation`](./research/prime-offset-formulation.md).
The new analytic decomposition note is
[`sieve target`](./research/sieve-target.md).

## The Conjecture

For the first `n` primes, let `m_n` be the least integer `m > 1` such that
`p_1 ... p_n + m` is prime. Fortune's conjecture states that every such `m_n`
is prime.

In Lean:

`FortuneConjecture`

where `nthPrimorial n = ∏_{i < n} p_i` and `nthPrime i` are formalized from `Nat.nth Nat.Prime`.

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `Fortune.Defs` | Primorial-of-first-primes, least-offset predicates, conjecture statement | 0 |
| `Fortune.Basic` | Explicit values for `nthPrimorial (0..4)` and least offsets for `n = 1..4` | 0 |
| `Fortune.Structure` | Coprimality, divisibility-exclusion, and parity structure of Fortunate offsets | 0 |
| `Fortune.Existence` | Existence of offsets and existence/uniqueness of least offsets | 0 |
| `Fortune.Bounds` | `minFac` and growth lower bounds for Fortunate offsets | 0 |
| `Fortune.Literature` | Primorial interval theorems (Theorem 17/18 style) and Fortune-offset corollary | 0 |
| `Fortune.Bridge` | Route 1 bridges between indexed and threshold primorial models | 0 |
| `Fortune.ReductionBound` | Conditional Route 2.A derivation from interval-prime existence | 0 |
| `Fortune.IntervalExistence` | Route 2 equivalences: interval-prime existence ↔ reduction bound | 0 |
| `Fortune.Sieve` | Sifted-candidate formulation, full-sieve target, and sieve-to-prime upgrade | 0 |
| `Fortune.IntervalExistenceSmall` | Finite (`1 <= n <= 17`) interval-existence and reduction-bound verification | 0 |
| `Fortune.Reduction` | Route 2.B reduction: quantitative bound implies `FortuneConjecture` | 0 |
| `Fortune.Congruence` | Route 3 congruence obstructions for indexed/threshold least offsets | 0 |
| `Fortune.Profile` | Route 4 prime-divisor profile strengthening | 0 |
| `Fortune.LowerInterval` | Route 5 tightened lower-interval theorem variant | 0 |
| `Fortune.CertifiedRange` | Route 6 certified finite extension (`1 <= n <= 17`) | 0 |
| `Fortune.Progress` | Route-level status statements and proved implications | 0 |
| `Fortune.SmallCases` | Finite-range theorem for `1 <= n <= 4` | 0 |
| `Fortune.Conjecture` | Verified finite range through `17`, plus the main open statement and expanded form | 1 |

## Route Progress

| Route | Lean statement(s) | Status |
|-------|-------------------|--------|
| 1.A/1.B/1.C (bridges) | `Route1PrimorialBridge`, `Route1LeastOffsetBridge`, `Route1NextPrimeWitness` | proved |
| 2.A (quantitative bound) | `Route2ReductionBound` | equivalent to `Route2IntervalPrimeExistence`; proved for `1 <= n <= 17` |
| 2.C (prime-offset strengthening) | `Route2PrimeOffsetPrimeExistence` | open, formally equivalent to Route 2 interval-prime existence, and implies `FortuneConjecture` |
| 2.D (full-sieve target) | `Route2FullSiftedPrimeOffsetExistence` | open, but formally shown to imply Route 2.C and hence `FortuneConjecture` |
| 2.E (full window-sieve target) | `Route2FullWindowSiftedPrimeOffsetExistence` | open, formally equivalent in force to checking only primes `q < ell <= q# + r^2`, and implies `FortuneConjecture` |
| 2.F (window-rough + square bound) | `Route2WindowRoughLowerBound Z` + `Route2SquareSieveLevel Z` | formally shown to imply Route 2.C and hence `FortuneConjecture` |
| 2.G (canonical square-root window-sifted target) | `Route2CanonicalSquareWindowSiftedExistence` | open, now formally shown to imply Route 2.C and hence `FortuneConjecture` |
| 2.H (canonical square-root window-rough target) | `Route2CanonicalSquareWindowRoughExistence` | open, now the sharpest single canonical analytic target in the project, and implies `FortuneConjecture` |
| 2.B (reduction theorem) | `Route2BoundImpliesFortune` | proved |
| 3 (congruence obstructions) | `Route3CongruenceObstructions` | proved |
| 4 (prime-divisor profile) | `Route4PrimeDivisorProfile` | proved (coprimality + all nontrivial divisors exceed `lastIncludedPrime n`) |
| 5 (tightened lower interval) | `Route5LowerIntervalTightening` | proved |
| 6 (certified finite range) | `Route6CertifiedRange` | proved for `1 <= n <= 17` |
| Main conjecture | `fortune_conjecture` | open |

## Structural Result Inventory

| Result | Lean theorem | Status |
|--------|--------------|--------|
| Every `n` has a Fortunate offset candidate | `exists_fortunateOffset` | proved |
| Every `n` has a least Fortunate offset | `exists_leastFortunateOffset` / `hasLeastFortunateOffset` | proved |
| Least Fortunate offsets are unique | `leastFortunateOffset_unique` / `existsUnique_leastFortunateOffset` | proved |
| Any Fortunate offset is coprime to the indexed primorial | `fortunateOffset_coprime_nthPrimorial` | proved |
| Any Fortunate offset is coprime to `primorial (lastIncludedPrime n)` | `fortunateOffset_coprime_primorial_lastIncludedPrime` | proved |
| Any least offset is coprime to `primorial (lastIncludedPrime n)` | `leastOffset_coprime_primorial_lastIncludedPrime` | proved |
| No included prime divides a least offset (indexed congruence form) | `leastFortunateOffset_not_modEq_zero_nthPrime` | proved |
| Prime divisors of least offsets are above `lastIncludedPrime n` | `prime_divisor_gt_lastIncludedPrime_of_leastOffset` | proved |
| Any nontrivial divisor of least offsets is above `lastIncludedPrime n` | `divisor_gt_lastIncludedPrime_of_leastOffset` | proved |
| Primorial upper-interval primality criterion (`q# + 1 < p < q# + r^2`) | `prime_sub_primorial_of_interval` | proved |
| Upper-interval existence as `p`-form ↔ offset `k`-form | `intervalPrimeExistsAtPrime_iff_offsetPrimeExistsAtPrime` | proved |
| Prime-offset strengthening implies the offset-form interval statement | `offsetPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime` | proved |
| Prime-offset strengthening implies the interval-prime statement | `intervalPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime` | proved |
| Under consecutive primes, the interval-prime statement implies the prime-offset formulation | `primeOffsetPrimeExistsAtPrime_of_intervalPrimeExistsAtPrime` | proved |
| Primes `<= q` cannot divide `q# + m` when `m` is prime and `m > q` | `primeOffset_not_dvd_primorial_add_of_prime_le` | proved |
| Full and windowed sifted candidates are equivalent | `siftedPrimeOffsetCandidateAtPrime_iff_windowSiftedPrimeOffsetCandidateAtPrime` | proved |
| Full and windowed sifted existence statements are equivalent | `siftedPrimeOffsetExistsAtPrime_iff_windowSiftedPrimeOffsetExistsAtPrime` | proved |
| A prime translate automatically gives a window-sifted candidate at any sieve level | `windowSiftedPrimeOffsetCandidateAtPrime_of_primeTranslate` | proved |
| Window-sifted candidates become window-rough below the translate | `windowRoughPrimeOffsetCandidateAtPrime_of_windowSiftedPrimeOffsetCandidateAtPrime` | proved |
| Canonical square-root sieve level dominates the full interval | `fullSieveLevelAtPrime_le_canonicalSquareSieveLevelAtPrime_sq` | proved |
| The next consecutive prime obeys Euclid's bound `r <= q# + 1` | `nextPrime_le_primorial_add_one` | proved |
| Full-sieve candidate implies primality of the translate | `prime_translate_of_siftedPrimeOffsetCandidateAtPrime` | proved |
| Full window-sieve candidate implies primality of the translate | `prime_translate_of_windowSiftedPrimeOffsetCandidateAtPrime` | proved |
| Window-rough candidate plus square bound implies primality of the translate | `prime_translate_of_windowRoughPrimeOffsetCandidateAtPrime` | proved |
| Prime-offset existence implies canonical square-root window-sifted existence | `canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime` | proved |
| Full-sieve existence implies the prime-offset formulation | `primeOffsetPrimeExistsAtPrime_of_fullSiftedPrimeOffsetExistsAtPrime` | proved |
| Full window-sieve existence implies the prime-offset formulation | `primeOffsetPrimeExistsAtPrime_of_fullWindowSiftedPrimeOffsetExistsAtPrime` | proved |
| Window-rough existence plus square bound implies the prime-offset formulation | `primeOffsetPrimeExistsAtPrime_of_windowRoughPrimeOffsetExistsAtPrime` | proved |
| Canonical square-root window-sifted existence implies the prime-offset formulation | `primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime` | proved |
| Canonical square-root window-rough existence implies the prime-offset formulation | `primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowRoughPrimeOffsetExistsAtPrime` | proved |
| Route 2 bridge equivalence (`interval existence ↔ reduction bound`) | `route2_intervalPrimeExistence_iff_reductionBound` | proved |
| Route 2 interval-prime existence and prime-offset existence are equivalent | `route2_intervalPrimeExistence_iff_primeOffsetPrimeExistence` | proved |
| Route 2 prime-offset strengthening implies the reduction bound | `route2_reductionBound_of_primeOffsetPrimeExistence` | proved |
| Route 2 prime-offset strengthening implies Fortune's conjecture | `route2_fortune_of_primeOffsetPrimeExistence` | proved |
| Route 2 full-sieve target implies the prime-offset formulation | `route2_primeOffsetPrimeExistence_of_fullSiftedPrimeOffsetExistence` | proved |
| Route 2 full-sieve target implies Fortune's conjecture | `route2_fortune_of_fullSiftedPrimeOffsetExistence` | proved |
| Route 2 sieve and window-sieve lower bounds are equivalent | `route2SieveLowerBound_iff_route2WindowSieveLowerBound` | proved |
| Route 2 full window-sieve target implies the prime-offset formulation | `route2_primeOffsetPrimeExistence_of_fullWindowSiftedPrimeOffsetExistence` | proved |
| Route 2 full window-sieve target implies Fortune's conjecture | `route2_fortune_of_fullWindowSiftedPrimeOffsetExistence` | proved |
| Route 2 window-rough lower bound plus square sieve level implies the prime-offset formulation | `route2_primeOffsetPrimeExistence_of_windowRoughLowerBound_and_squareSieveLevel` | proved |
| Route 2 window-rough lower bound plus square sieve level implies Fortune's conjecture | `route2_fortune_of_windowRoughLowerBound_and_squareSieveLevel` | proved |
| Route 2 canonical square-root window-sifted target implies the prime-offset formulation | `route2_primeOffsetPrimeExistence_of_canonicalSquareWindowSiftedExistence` | proved |
| Route 2 canonical square-root window-sifted target implies Fortune's conjecture | `route2_fortune_of_canonicalSquareWindowSiftedExistence` | proved |
| Route 2 canonical square-root window-rough target implies the prime-offset formulation | `route2_primeOffsetPrimeExistence_of_canonicalSquareWindowRoughExistence` | proved |
| Route 2 canonical square-root window-rough target implies Fortune's conjecture | `route2_fortune_of_canonicalSquareWindowRoughExistence` | proved |
| Finite route-2 prime-offset existence (`1 <= n <= 17`) | `route2_primeOffsetPrimeExistence_one_to_seventeen_progress` | proved |
| Finite route-2 canonical square-root window-sifted existence (`1 <= n <= 17`) | `route2_canonicalSquareWindowSiftedExistence_one_to_seventeen_progress` | proved |
| Finite route-2 interval existence (`1 <= n <= 17`) | `route2_intervalPrimeExistence_one_to_seventeen` | proved |
| Finite route-2 reduction bound (`1 <= n <= 17`) | `route2_reductionBound_one_to_seventeen` | proved |
| Finite route-2 interval existence (`1 <= n <= 16`) | `route2_intervalPrimeExistence_one_to_sixteen` | proved |
| Finite route-2 reduction bound (`1 <= n <= 16`) | `route2_reductionBound_one_to_sixteen` | proved |
| Finite route-2 interval existence (`1 <= n <= 15`) | `route2_intervalPrimeExistence_one_to_fifteen` | proved |
| Finite route-2 reduction bound (`1 <= n <= 15`) | `route2_reductionBound_one_to_fifteen` | proved |
| Finite route-2 interval existence (`1 <= n <= 12`) | `route2_intervalPrimeExistence_one_to_twelve` | proved |
| Finite route-2 reduction bound (`1 <= n <= 12`) | `route2_reductionBound_one_to_twelve` | proved |
| Finite route-2 interval existence (`1 <= n <= 6`) | `route2_intervalPrimeExistence_one_to_six` | proved |
| Finite route-2 reduction bound (`1 <= n <= 6`) | `route2_reductionBound_one_to_six` | proved |
| Finite route-2 interval existence (`1 <= n <= 5`) | `route2_intervalPrimeExistence_one_to_five` | proved |
| Finite route-2 reduction bound (`1 <= n <= 5`) | `route2_reductionBound_one_to_five` | proved |
| Primorial lower-interval primality criterion (tightened side condition) | `prime_primorial_sub_of_interval_tight` | proved |
| Verified finite range of the conjecture (`1 <= n <= 17`) | `fortune_conjecture_one_to_seventeen` | proved |
| Verified finite range of the conjecture (`1 <= n <= 16`) | `fortune_conjecture_one_to_sixteen` | proved |
| Verified finite range of the conjecture (`1 <= n <= 15`) | `fortune_conjecture_one_to_fifteen` | proved |
| Verified finite range of the conjecture (`1 <= n <= 12`) | `fortune_conjecture_one_to_twelve` | proved |
| Certified finite range extension | `hasPrimeLeastFortunateOffset_one_to_seventeen` | proved |

The interval criteria above correspond to the Fortune-adjacent primorial theorems
discussed in Čejchan–Křížek–Somer (Rocky Mountain J. Math., 2018); see
[`references.md`](../../references.md#number-theory).

For the current research direction, see
[`research/prime-offset-formulation.md`](./research/prime-offset-formulation.md).
For the sharpened analytic target, see
[`research/sieve-target.md`](./research/sieve-target.md).

## Building

```sh
lake update && lake build
```
