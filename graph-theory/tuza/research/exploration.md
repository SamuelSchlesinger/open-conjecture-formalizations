# Tuza's conjecture — computational exploration

Script: `explore.py`. For each graph it computes `ν` (max edge-disjoint triangle
packing, by branch-and-bound) and `τ` (min triangle edge cover, by search in
increasing size), checks the proved sandwich `ν ≤ τ ≤ 3ν` (as an `assert`), and
tests the conjecture `τ ≤ 2ν`.

## Exhaustive over all labelled graphs, `n ≤ 5`

| n | graphs with triangles | violations of τ≤2ν | max τ/ν | # tight (τ=2ν) |
|---|---|---|---|---|
| 3 | 1   | 0 | 1 | 0 |
| 4 | 23  | 0 | 2 | 1 |
| 5 | 636 | 0 | 2 | 26 |

The sandwich `ν ≤ τ ≤ 3ν` held for **every** graph (the `assert` never fired) —
a check on the Lean theorems `nu_le_tau` and `tau_le_three_mul_nu`. The
conjecture `τ ≤ 2ν` held with **zero violations**, and the ratio `τ/ν` reaches
its maximum `2` — so the factor `2` is attained, not merely approached.

**Smallest tight example: `K₄`.** The unique tight graph on 4 vertices is the
complete graph (all 6 edges) — exactly the `Tightness.tuza_tight` witness
(`ν = 1`, `τ = 2`). The 26 tight graphs on 5 vertices are all `K₄`-with-extra
(an isolated/pendant vertex, etc.).

## Random graphs, `n = 6, 7`

| n | sampled (with triangles) | violations | max τ/ν | # tight |
|---|---|---|---|---|
| 6 | 2820 | 0 | 2 | 84 |
| 7 | 1484 | 0 | 2 | 13 |

No violation in any graph examined; the maximum ratio stays exactly `2`.

## Cross-check against the Lean theorems

| fact | exploration | Lean |
|---|---|---|
| `ν ≤ τ` | assert held | `Basic.nu_le_tau` |
| `τ ≤ 3ν` | assert held | `Bounds.tau_le_three_mul_nu` |
| `K₄`: `ν=1, τ=2` | smallest tight graph | `Tightness.nu_K4`, `tau_K4`, `tuza_tight` |
| `τ ≤ 2ν` (n≤5, random n≤7) | 0 violations | headline `sorry` |

## The open frontier

`τ ≤ 2ν` is open in general (Tuza 1981). Known: planar graphs (Tuza 1990),
`K₄`-free graphs, the fractional relaxation `τ* ≤ 2ν*` (Krivelevich 1995); the
best proved constant is `τ ≤ (3 − 3/23)ν ≈ 2.87ν` (Haxell 1999), improving the
elementary `τ ≤ 3ν` formalized here. The factor `2` cannot be lowered (`K₄`).
