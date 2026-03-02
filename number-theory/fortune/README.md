# Fortune's Conjecture

A Lean 4 formalization scaffold for Fortune's conjecture.

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
| `Fortune.IntervalExistenceSmall` | Finite (`1 <= n <= 5`) interval-existence and reduction-bound verification | 0 |
| `Fortune.Reduction` | Route 2.B reduction: quantitative bound implies `FortuneConjecture` | 0 |
| `Fortune.Congruence` | Route 3 congruence obstructions for indexed/threshold least offsets | 0 |
| `Fortune.Profile` | Route 4 prime-divisor profile strengthening | 0 |
| `Fortune.LowerInterval` | Route 5 tightened lower-interval theorem variant | 0 |
| `Fortune.CertifiedRange` | Route 6 certified finite extension (`1 <= n <= 5`) | 0 |
| `Fortune.Progress` | Route-level status statements and proved implications | 0 |
| `Fortune.SmallCases` | Finite-range theorem for `1 <= n <= 4` | 0 |
| `Fortune.Conjecture` | Main open statement and expanded form | 1 |

## Route Progress

| Route | Lean statement(s) | Status |
|-------|-------------------|--------|
| 1.A/1.B/1.C (bridges) | `Route1PrimorialBridge`, `Route1LeastOffsetBridge`, `Route1NextPrimeWitness` | proved |
| 2.A (quantitative bound) | `Route2ReductionBound` | equivalent to `Route2IntervalPrimeExistence`; proved for `1 <= n <= 5` |
| 2.B (reduction theorem) | `Route2BoundImpliesFortune` | proved |
| 3 (congruence obstructions) | `Route3CongruenceObstructions` | proved |
| 4 (prime-divisor profile) | `Route4PrimeDivisorProfile` | proved (coprimality + all nontrivial divisors exceed `lastIncludedPrime n`) |
| 5 (tightened lower interval) | `Route5LowerIntervalTightening` | proved |
| 6 (certified finite range) | `Route6CertifiedRange` | proved for `1 <= n <= 5` |
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
| Route 2 bridge equivalence (`interval existence ↔ reduction bound`) | `route2_intervalPrimeExistence_iff_reductionBound` | proved |
| Finite route-2 interval existence (`1 <= n <= 5`) | `route2_intervalPrimeExistence_one_to_five` | proved |
| Finite route-2 reduction bound (`1 <= n <= 5`) | `route2_reductionBound_one_to_five` | proved |
| Primorial lower-interval primality criterion (tightened side condition) | `prime_primorial_sub_of_interval_tight` | proved |
| Certified finite range extension | `hasPrimeLeastFortunateOffset_one_to_five` | proved |

The interval criteria above correspond to the Fortune-adjacent primorial theorems
discussed in Čejchan–Křížek–Somer (Rocky Mountain J. Math., 2018); see
[`references.md`](../../references.md#number-theory).

## Building

```sh
lake update && lake build
```
