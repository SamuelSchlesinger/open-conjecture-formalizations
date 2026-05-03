# Frankl's Union-Closed Sets Conjecture

A Lean 4 formalization scaffold for Frankl's union-closed sets conjecture.

## The Conjecture

For every finite nontrivial union-closed family of finite sets, some element
belongs to at least half of the member-sets.

In Lean, a family is represented as `Finset (Finset α)`, and the half-bound is
written without division:

`F.card ≤ 2 * memberCount x F`

## Current Formalized Territory

The project proves the standard singleton-containing case. If a union-closed
family contains `{x}`, then the map `A ↦ insert x A` injects the member-sets
omitting `x` into the member-sets containing `x`; hence `x` occurs in at least
half the family.

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `Frankl.Defs` | Finite families, union-closedness, member counts, conjecture statements | 0 |
| `Frankl.Basic` | Membership lemmas and the singleton-containing case | 0 |
| `Frankl.SmallCases` | Empty and one-member family sanity checks | 0 |
| `Frankl.Conjecture` | Main open global statement and expanded form | 1 |

## Building

```sh
lake update && lake build
```
