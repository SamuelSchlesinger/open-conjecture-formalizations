# New Mersenne Conjecture

A Lean 4 formalization scaffold for the New Mersenne conjecture.

## The Conjecture

For odd integers `p`, consider the three conditions:

1. `p` has one of the special forms
   `2^k - 1`, `2^k + 1`, `4^k - 3`, `4^k + 3`,
2. `2^p - 1` is prime,
3. `(2^p + 1) / 3` is prime (with divisibility by `3`).

The New Mersenne conjecture states that for odd `p`, any two imply the third.

In Lean:

`NewMersenneConjecture`

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `NewMersenne.Defs` | Shape predicates, Mersenne/Wagstaff exponent predicates, conjecture statement | 0 |
| `NewMersenne.Basic` | Explicit verified examples `p = 3, 5, 7` satisfying all three conditions | 0 |
| `NewMersenne.SmallCases` | Derived implication package for `p = 3, 5, 7` | 0 |
| `NewMersenne.Conjecture` | Main open statement and expanded form | 1 |

## Building

```sh
lake update && lake build
```
