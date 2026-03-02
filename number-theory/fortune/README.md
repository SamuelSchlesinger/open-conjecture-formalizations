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
| `Fortune.SmallCases` | Finite-range theorem for `1 <= n <= 4` | 0 |
| `Fortune.Conjecture` | Main open statement and expanded form | 1 |

## Structural Result Inventory

| Result | Lean theorem | Status |
|--------|--------------|--------|
| Every `n` has a Fortunate offset candidate | `exists_fortunateOffset` | proved |
| Every `n` has a least Fortunate offset | `exists_leastFortunateOffset` / `hasLeastFortunateOffset` | proved |
| Least Fortunate offsets are unique | `leastFortunateOffset_unique` / `existsUnique_leastFortunateOffset` | proved |
| Any Fortunate offset is coprime to the `n`-primorial | `fortunateOffset_coprime_nthPrimorial` | proved |
| No included prime divides a Fortunate offset | `fortunateOffset_not_dvd_nthPrime` / `fortunateOffset_not_dvd_firstPrimes` | proved |
| For `n ≥ 1`, the `n`-primorial is even | `nthPrimorial_even_of_one_le` | proved |
| For `n ≥ 1`, any Fortunate offset is odd | `fortunateOffset_odd_of_one_le` | proved |
| Lower bound by minimal prime factor | `minFac_gt_lastIncludedPrime_of_fortunateOffset` | proved |
| Composite-offset quadratic lower bound | `succ_lastIncludedPrime_sq_le_offset_of_composite_fortunateOffset` | proved |
| Primorial upper-interval primality criterion (`q# + 1 < p < q# + r^2`) | `prime_sub_primorial_of_interval` | proved |
| Primorial lower-interval primality criterion (`q# - s^2 < p < q# - 1`, with `q < p`) | `prime_primorial_sub_of_interval` | proved |
| Least-offset corollary from the interval criterion | `least_offset_prime_of_lt_nextPrime_sq` | proved |
| Fortune's conjecture (all least offsets are prime) | `fortune_conjecture` | open |

The interval criteria above correspond to the Fortune-adjacent primorial theorems
discussed in Čejchan–Křížek–Somer (Rocky Mountain J. Math., 2018); see
[`references.md`](../../references.md#number-theory).

## Building

```sh
lake update && lake build
```
