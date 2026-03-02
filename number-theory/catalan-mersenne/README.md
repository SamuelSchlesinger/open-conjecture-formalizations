# Catalan-Mersenne Conjecture

A Lean 4 formalization scaffold for the Catalan-Mersenne sequence and the
historical cutoff-style conjecture.

## The Sequence

Define:

- `c_0 = 2`,
- `c_{n+1} = 2^{c_n} - 1`.

In Lean this is `catalanMersenne : Nat → Nat`.

## Conjecture Formalized

Historically the conjecture is often described as "terms are prime up to some
limit." We formalize this as:

- there exists `N` such that all terms up to `N` are prime, and
- all terms after `N` are composite.

In Lean:

`CatalanMersenneCutoffConjecture`

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `CatalanMersenne.Defs` | Recursive sequence, primality predicate, cutoff conjecture statement | 0 |
| `CatalanMersenne.Basic` | Explicit values and primality for indices `0..3` | 0 |
| `CatalanMersenne.SmallCases` | Finite-range primality theorem and initial-prime-block existence | 0 |
| `CatalanMersenne.Conjecture` | Main open cutoff statement and expanded form | 1 |

## Building

```sh
lake update && lake build
```
