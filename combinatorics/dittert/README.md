# Dittert Conjecture

A Lean 4 formalization scaffold for the Dittert conjecture on matrices in the
domain `K_n`.

## The Setup

For `n × n` real matrices, define:

- `K_n`: matrices with nonnegative entries and total sum `n`,
- `R(A)`: product of row sums,
- `C(A)`: product of column sums,
- `per(A)`: matrix permanent.

We formalize Dittert's objective as:

`F(A) = R(A) + C(A) - per(A)`.

## Conjecture Formalized

For each `n > 0`, the uniform matrix (all entries `1/n`) maximizes `F` on
`K_n`, and equality occurs only at the uniform matrix.

In Lean:

- `DittertConjectureAt n`
- `DittertConjecture`

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `Dittert.Defs` | `K_n`, row/column products, permanent functional, uniform matrix, conjecture statements | 0 |
| `Dittert.Basic` | Uniform-entry lemmas, `K_1` characterization, exact `F` value at uniform `1×1` matrix | 0 |
| `Dittert.SmallCases` | Fully proved base case `n = 1` | 0 |
| `Dittert.Conjecture` | Main open global statement and expanded form | 1 |

## Building

```sh
lake update && lake build
```
