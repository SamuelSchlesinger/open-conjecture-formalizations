# Gold Partition Conjecture

A Lean 4 formalization scaffold for the Gold partition conjecture in finite
order theory.

## Conjecture Form

For a finite poset that is not a chain, one seeks two consecutive comparisons
for which, along each branch, the number of compatible linear extensions
satisfies an inequality of the form:

`t₀ ≥ t₁ + t₂`

where `t₀` is the original count, `t₁` is the count after one comparison
outcome, and `t₂` is the count after two comparison outcomes.

This project formalizes an adaptive two-step comparison plan (second query may
depend on first outcome) over `Fin n`.

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `GoldPartition.Defs` | Finite-poset relation axioms, linear extensions via permutations, outcome-conditioned counts, conjecture statement | 0 |
| `GoldPartition.Basic` | Foundational lemmas (`eqRel`, nonnegativity, order-preservation for equality relation) | 0 |
| `GoldPartition.SmallCases` | Vacuous base cases for `n = 0, 1` (no non-chain relation possible) | 0 |
| `GoldPartition.Conjecture` | Main open statement and expanded form | 1 |

## Building

```sh
lake update && lake build
```
