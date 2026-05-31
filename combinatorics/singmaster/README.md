# Singmaster's Conjecture

A Lean 4 / Mathlib formalization of **Singmaster's conjecture**: every integer
`a ≥ 2` occurs only a bounded number of times in Pascal's triangle.

## The conjecture

For `a ≥ 2`, let the *Singmaster multiplicity* be

```
N(a) = #{ (n,k) : 0 ≤ k ≤ n,  C(n,k) = a }.
```

> **Conjecture (Singmaster 1971).** There is a constant `C` with `N(a) ≤ C` for
> every `a ≥ 2`.

Singmaster conjectured `C = 8`: no number is known to appear more than `8`
times, the record being `3003 = C(3003,1) = C(78,2) = C(15,5) = C(14,6)` (with
symmetric partners). The best *proved* upper bound is only
`N(a) = O(log a / log log a)` (Singmaster 1971; Abbott–Erdős–Hanson) — a constant
bound is open.

## How it is modeled

For `a ≥ 2` every occurrence has `n ≤ a` (away from the `1`-valued ends,
`C(n,k) ≥ n`, the row minimum — `Basic.self_le_choose`), so all occurrences live
in the finite box `{0,…,a}²` and

```
singmasterCount a = #{ (n,k) ∈ {0,…,a}² : k ≤ n ∧ C(n,k) = a }
```

is an honest, **computable** `Finset` cardinality equal to `N(a)`
(`Basic.le_of_choose_eq` justifies completeness). Small cases are therefore
decidable by the kernel (`decide`, no `native_decide`). For `a ≤ 1` the box
undercounts (`1` occurs infinitely often), which is why the conjecture is stated
for `a ≥ 2`.

## Formalized territory

| Module | Contents | `sorry` |
|--------|----------|:-------:|
| `Defs` | `occurrences`, `singmasterCount` = `N(a)`, `mem_occurrences`, headline `SingmasterConjecture` | 0 |
| `Basic` | **row-minimum** `n ≤ C(n,k)` for `0<k<n` (`self_le_choose`); **box completeness** `n ≤ a` (`le_of_choose_eq`); **`N(a) ≥ 2` for `a ≥ 3`** (`a = C(a,1) = C(a,a-1)`) | 0 |
| `SmallCases` | `N(2)=1`, `N(6)=3`, `N(10)=4` by `decide` (sanity check on the counter) | 0 |
| `Family` | **infinite family appearing ≥ 4 times**: `N(C(n,2)) ≥ 4` for all `n ≥ 5` (`four_le_singmasterCount_choose_two`); hence any Singmaster constant is `≥ 4` (`four_le_of_singmasterConjecture`) | 0 |
| `Conjecture` | the headline theorem — one intentional `sorry` | 1 |

Every result outside `Conjecture` is **`sorry`-free and axiom-clean** (only
`propext`, `Classical.choice`, `Quot.sound`; no `native_decide`). Verify with
`lake env lean scripts/axioms.lean`.

### Proved vs. open

Proved in full generality: the row-minimum bound and box completeness (so the
counter is faithful); `N(a) ≥ 2` for `a ≥ 3`; and the infinite `≥ 4` family,
pinning the conjectured constant from below (`4 ≤ C ≤ 8`). The uniform upper
bound — even *some* constant — is the open problem and the single `sorry`.

## Computational exploration (`research/`)

`research/explore.py` (results in `research/exploration.md`) computes `N(a)`
exactly for all `a ∈ [2, 10⁶]`:

- **maximum multiplicity is 8**, attained *uniquely* by `3003`;
- distribution: 998 266 values appear twice, 1 715 appear 4×, 10 appear 3×, six
  appear 6× (`120, 210, 1540, 7140, 11628, 24310`), one appears 8× (`3003`);
- **no `a ≤ 10⁶` appears 5 or 7 times** — interior occurrences come in mirror
  pairs, so odd multiplicities `> 3` require rare central coincidences;
- every `C(n,2)` (`n ≥ 5`) reaches `N ≥ 4`, matching the proved family.

## Building

```sh
lake update && lake build         # fetches Mathlib v4.28.0 (cache) and builds
lake env lean scripts/axioms.lean # audit: only core axioms (+ the one headline sorry)
python3 research/explore.py       # reproduce the exploration
```

Pinned to `leanprover/lean4:v4.28.0` and Mathlib `v4.28.0`.

## References

Singmaster, D. "How often does an integer occur as a binomial coefficient?"
*Amer. Math. Monthly* 78 (1971), 385–386. Abbott, Erdős, Hanson (1974); Kane
(2007) for the sharpest known upper bounds. Full citations in the repository
[`references.md`](../../references.md#combinatorics).

## Status

Formalization of *known territory* (faithful computable multiplicity, the trivial
`≥ 2` bound, and a proved infinite `≥ 4` family bounding the constant below) plus
the open headline conjecture as a single intentional `sorry`.
