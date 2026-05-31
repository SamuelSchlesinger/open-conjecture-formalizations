# Tuza's Conjecture

A Lean 4 / Mathlib formalization of **Tuza's conjecture** in graph theory:
the minimum number of edges needed to destroy all triangles of a graph is at
most twice the maximum number of edge-disjoint triangles.

## The conjecture

For a finite simple graph `G`:

* `ν(G)` = the largest number of pairwise **edge-disjoint** triangles (a *packing*);
* `τ(G)` = the smallest number of edges meeting **every** triangle (a *cover* —
  deleting them makes `G` triangle-free).

> **Conjecture (Zs. Tuza, 1981).** `τ(G) ≤ 2·ν(G)` for every finite graph `G`.

The factor `2` is best possible (`K₄` has `ν = 1`, `τ = 2`). The conjecture is
open; it is known for planar graphs, `K₄`-free graphs, and fractionally
(`τ* ≤ 2ν*`), with the best general constant `≈ 2.87` (Haxell 1999).

## How it is modeled

Everything lives in `Finset V`: a **triangle** is a 3-clique and an **edge** is a
2-clique, so the three edges of a triangle `t` are exactly its 2-element subsets,
`t.powersetCard 2`. A packing is a set of triangles with pairwise-disjoint edge
sets; a cover is a set of edges meeting every triangle's edge set. `ν` and `τ`
are `sSup`/`sInf` over the achievable packing/cover sizes — so no decidability
instances are needed for the general theory (the `K₄` facts are still discharged
by `decide`).

## Formalized territory

| Module | Contents | `sorry` |
|--------|----------|:-------:|
| `Defs` | `triangles`, `edges`, `triEdges`, `IsPacking`, `IsCover`, `ν = nu`, `τ = tau`, headline `TuzaConjecture` | 0 |
| `Basic` | `triEdges` facts (3 edges per triangle, all in `G`); `ν`, `τ` are attained; **`ν(G) ≤ τ(G)`** (edge-disjoint triangles use distinct cover edges) | 0 |
| `Bounds` | **`τ(G) ≤ 3·ν(G)`**: a *maximum* packing's `3ν` edges cover every triangle (maximality ⇒ every triangle meets the packing); gives the sandwich `ν ≤ τ ≤ 3ν` | 0 |
| `Tightness` | **`K₄`: `ν = 1`, `τ = 2`, so `τ = 2ν`** — the factor `2` is best possible (`K₄` facts by `decide`, bounds from the general API) | 0 |
| `Conjecture` | the headline theorem — one intentional `sorry` | 1 |

Every result outside `Conjecture` is **`sorry`-free and axiom-clean** (only
`propext`, `Classical.choice`, `Quot.sound`). Verify with
`lake env lean scripts/axioms.lean`.

### Proved vs. open

Proved in full generality: `ν` and `τ` are well-defined and attained; the
sandwich `ν(G) ≤ τ(G) ≤ 3·ν(G)`; and tightness of the constant `2` via `K₄`.
The conjecture `τ ≤ 2ν` itself is the open problem and the single `sorry`.

## Computational exploration (`research/`)

`research/explore.py` (results in `research/exploration.md`):

- `τ ≤ 2ν` holds on **all** labelled graphs with `n ≤ 5` and ~4300 random graphs
  at `n = 6, 7` — **zero violations**;
- the proved sandwich `ν ≤ τ ≤ 3ν` holds everywhere (a check on the Lean theorems);
- the maximum ratio `τ/ν` is exactly `2`, attained; the **smallest tight graph is
  `K₄`** (matching `Tightness.tuza_tight`).

## Building

```sh
lake update && lake build         # fetches Mathlib v4.28.0 (cache) and builds
lake env lean scripts/axioms.lean # axiom audit (+ the one headline sorry)
python3 research/explore.py       # reproduce the exploration
```

Pinned to `leanprover/lean4:v4.28.0` and Mathlib `v4.28.0`.

## References

Tuza, Zs. "Conjecture" in *Finite and Infinite Sets* (1981). Tuza, Zs. "A
conjecture on triangles of graphs." *Graphs Combin.* 6 (1990), 373–380. Haxell,
P. "Packing and covering triangles in graphs." *Discrete Math.* 195 (1999),
251–254. Krivelevich, M. "On a conjecture of Tuza about packing and covering of
triangles." *Discrete Math.* 142 (1995), 281–286. Full citations in
[`references.md`](../../references.md#graph-theory).

## Status

Formalization of known territory — the sandwich `ν ≤ τ ≤ 3ν` and tightness of the
factor `2` (`K₄`) — with the open conjecture `τ ≤ 2ν` as a single intentional
`sorry`.
