# The 1/3–2/3 Conjecture

A Lean 4 / Mathlib formalization of the **1/3–2/3 conjecture** in finite order
theory, with proved "known territory," two genuine reductions, and a documented
computational exploration of the open frontier.

## The conjecture

Let `P = (X, ≤)` be a finite poset. A *linear extension* is a total order
containing `≤`. Write `e(P)` for the number of linear extensions and, for an
incomparable pair `x ∥ y`, write `e(P, x<y)` for the number of extensions
placing `x` before `y`, so

```
δ(x,y) = e(P, x<y) / e(P) ∈ (0,1).
```

> **Conjecture (Kislitsyn 1968; Fredman; Linial 1984).** Every finite poset that
> is *not a chain* has an incomparable pair `{x, y}` with `1/3 ≤ δ(x,y) ≤ 2/3`.

It is open since 1968. The best known general bound is
`δ(P) ≥ (5 − √5)/10 ≈ 0.2764` (Brightwell–Felsner–Trotter 1995, via
Ahlswede–Daykin/FKG); the gap to `1/3 ≈ 0.3333` is the open problem. Equivalent
algorithmic content: a single comparison always splits the linear extensions by
a factor `≤ 2/3`, giving `O(log e(P))` sorting under partial information.

## How it is modeled

A linear extension is encoded as a **ranking** — an injective, monotone map
`f : X → Fin |X|` (`a ≤ b → f a ≤ f b`). For `|X| = n` an injective map to
`Fin n` is a bijection, and monotonicity makes the pullback a linear order
containing `≤`; the correspondence with linear extensions is bijective. The set
of rankings is a genuine `Finset`, so

```
e(P)      = numLinExts      = (linExts).card                         -- computable
e(P, x<y) = numBefore x y   = (linExts.filter (f x < f y)).card      -- computable
```

are honest cardinalities — small posets are decidable by the kernel (`decide`,
no `native_decide`). The conjecture is stated fraction-free (mirroring the
Frankl project's `|F| ≤ 2·count`): a pair is *balanced* when
`e(P) ≤ 3·e(P,x<y)` and `3·e(P,x<y) ≤ 2·e(P)`. This is a more computable
formulation than the `OrderHom`/`Set.ncard` statement in
`google-deepmind/formal-conjectures`.

## Formalized territory

| Module | Contents | `sorry` |
|--------|----------|:-------:|
| `Defs` | poset model; `IsLinExt`, `linExts`, `numLinExts` = `e(P)`, `numBefore` = `e(P,x<y)`; `Incomp`, fraction-free `IsBalancedPair`, `IsNotChain`; the headline `OneThirdTwoThirdsConjecture` | 0 |
| `Basic` | **partition identity** `e(P,x<y)+e(P,y<x)=e(P)`; **`e(P) > 0`** (finite Szpilrajn via `toLinearExtension` + `monoEquivOfFin`); balanced-pair symmetry; chain ⇔ non-totality | 0 |
| `Nontrivial` | **`δ(x,y) ∈ (0,1)`** for incomparable pairs (`0 < e(P,x<y) < e(P)`): both orders are realized, by augmenting `≤` with the forced relation `x<y` (still a poset) and extending | 0 |
| `SmallCases` | chains satisfy the conjecture vacuously; the tight 3-element poset `V3` (`a<b`, `c` free): `e=3`, balanced pair `{a,c}`, and **tightness** `V3_balance_tight` — every incomparable pair has `min`-balance exactly `1/3`, so `1/3` is best possible (Linial) | 0 |
| `Duality` | **`δ(P) = δ(Pᵒᵈ)`**: order reversal `f ↦ Fin.rev ∘ f` is a bijection of linear extensions, giving `e(Pᵒᵈ)=e(P)`, `e(Pᵒᵈ,x<y)=e(P,y<x)`, and the conjecture is self-dual | 0 |
| `Symmetry` | an incomparable pair swapped by an **order-automorphism** is balanced with `δ=1/2`; hence a poset with a pair of **twins** (interchangeable elements) satisfies the conjecture — the order-theoretic analogue of Frankl twin-deletion; **antichains** (discrete order) are a special case | 0 |
| `DisjointUnion` | the **parallel composition `P ⊕ P`** satisfies the conjecture: the copy-swap automorphism makes `{inl x, inr x}` balanced (`δ=1/2`) — a balanced pair that is *not* a twin pair, so it genuinely uses the global-automorphism lemma beyond the local twin condition | 0 |
| `AddTop` | **adding a global maximum preserves all balance**: `e(WithTop P)=e(P)` and `e(WithTop P,↑x<↑y)=e(P,x<y)`, so the conjecture for `WithTop P` reduces to `P` (`oneThirdTwoThirdsFor_withTop`). The crux is the *forcing* lemma — `⊤` lands on the top `Fin`-position — plus a linear-extension counting bijection across the `\|P\|→\|P\|+1` boundary (the ordinal-sum reduction for a one-point top summand) | 0 |
| `OrdinalSum` | **the full ordinal-sum reduction `P ⊕ Q`**: `e(P⊕Q)=e(P)·e(Q)` (`numLinExts_ser`), `e(P⊕Q,↑x<↑y)=e(P,x<y)·e(Q)` / `e(P)·e(Q,x<y)` (`numBefore_ser_inl/inr`), so balance is preserved on each block and **the conjecture for `P⊕Q` reduces to `P` and `Q`** (`oneThirdTwoThirdsFor_ser`) — i.e. to ordinal-sum-**indecomposable** posets. The crux is the set-partition *forcing* lemma (the `\|P\|` bottom block occupies the bottom positions, by pigeonhole) + a counting bijection `linExts(P⊕Q) ≃ linExts P × linExts Q` | 0 |
| `ParallelSum` | **the disjoint-union (parallel) reduction `P ⊔ Q`**: the **shuffle formula** `e(P⊔Q)=C(\|P\|+\|Q\|,\|P\|)·e(P)·e(Q)` (`numLinExts_par_eq_choose`) and `e(P⊔Q,↑x<↑y)=e(P,x<y)·C·e(Q)` (`numBefore_par_inl/inr`), so the shuffle factor cancels and **internal pairs keep their balance** (`isBalancedPair_par_inl/inr`). Hence a non-chain summand's balanced pair survives (`oneThirdTwoThirdsFor_par_of_left/_right`); the full reduction `oneThirdTwoThirdsFor_par` holds modulo a `hcross` hypothesis isolating the genuinely harder **two-chains** case (witness must be a *cross* pair). The crux is the *order-iso reindexing* `Finset.orderIsoOfFin` of the **varying** `\|P\|`-subset of positions (unlike the fixed bottom block of `OrdinalSum`) | 0 |
| `TwoChains` | the **discrete first-crossing** lemma `balanced_of_monotone_steps` (a before-count sequence with steps `≤ D/3` that starts `≤ 2D/3` and reaches `≥ D/3` must hit the balanced band — the IVT heart, needing *no* monotonicity), and the **step-bound inequality** `step_bound_arith` (`(m+n)(m+n−1) ≥ 3mn`) | 0 |
| `TwoChainsCount` | the **two-chains kernel**, fully counted. A chain `Fin k` has a unique linear extension (`numLinExts_fin`); the **cross before-count** `e(Fin m⊔Fin n, b_j<a₀)=C(m+n−1−j,m)` (`numBefore_inr_inl_finSum`) via the bijection `F ↦ posSet F` (a chain extension is determined by its position-set) + subset counting; the binomial step bounds (`three_choose_le`, via the exact ratio identity from factorials); and the **row-case** `balancedPair_finSum_row` — feeding all this to `balanced_of_monotone_steps` produces a balanced cross pair when `m ≤ 2n` | 0 |
| `SeriesParallel` | the **series-parallel theorem**. Order-iso transfer of every quantity (`isBalancedPair_orderIso`, `oneThirdTwoThirdsFor_orderIso`); the full two-chains kernel `balancedPair_finSum` (both regimes, `m>2n` via the summand-swap); and **the conjecture for any disjoint union of two chains** (`oneThirdTwoThirdsFor_par_chains`, transporting the kernel along `P≃o Fin\|P\|`). This **discharges `hcross`**, making the disjoint-union reduction **unconditional** (`oneThirdTwoThirdsFor_par_total`). With the ordinal-sum reduction, this proves **1/3–2/3 for every series-parallel poset** | 0 |
| `Width2` | width hierarchy; **width ≤ 1 ⇔ chain** (proved); precise statement of Linial's width-2 theorem `LinialWidthTwo` as the next analytic target | 0 |
| `Conjecture` | the headline theorem — one intentional `sorry` | 1 |

Every result outside `Conjecture` is **`sorry`-free and axiom-clean** (only
`propext`, `Classical.choice`, `Quot.sound`; no `native_decide`). Verify with
`lake env lean scripts/axioms.lean`.

### What is *proved* vs. *open*

Proved, in full generality (sorry-free, axiom-clean): the counting
infrastructure and partition identity; `e(P) > 0`; **`δ(x,y) ∈ (0,1)`** for
incomparable pairs; the min-form `δ(P) = max min ≥ 1/3` characterization;
tightness of `1/3`; the **duality** reduction; the **twin / symmetry** case (any
poset with an incomparable automorphism-swapped pair); **antichains** (`δ=1/2`);
the **parallel composition `P ⊕ P`**; the **add-a-maximum reduction** (`WithTop`);
the **full ordinal-sum reduction `P ⊕ Q`** (to series-indecomposable posets); the
**shuffle formula** `e(P⊔Q)=C(\|P\|+\|Q\|,\|P\|)·e(P)·e(Q)`; the **unconditional
disjoint-union reduction** (`oneThirdTwoThirdsFor_par_total`); the **two-chains
kernel** — every `Fin m ⊔ Fin n` has a balanced cross pair, via a discrete
intermediate-value argument on the exact cross before-count
`e(·,b_j<a₀)=C(m+n−1−j,m)`; the **order-isomorphism transfer** of `IsBalancedPair`;
and hence — by structural induction over the two now-total reductions — **the
1/3–2/3 conjecture for every series-parallel poset**; and **width ≤ 1 ⇔ chain**.
Together the duality + ordinal-sum + disjoint-union reductions reduce the *general*
conjecture to **connected, series-indecomposable** posets with no global extremum.
Stated precisely but **not** formalized (known hard theorems): Linial's width-2
theorem, and the constant bounds (Kahn–Saks `3/11`, BFT `(5−√5)/10`). The full
conjecture remains the single `sorry`.

## Computational exploration (`research/`)

`research/explore.py` and `research/explore_large.py` (results in
`research/exploration.md`):

- **Verified** `δ(P) ≥ 1/3` for *all* labelled posets with `n ≤ 5` (zero
  violations) and ≈3000 random posets each at `n = 6..9`. The minimum `1/3` is
  *attained*, not approached.
- **Extremal structure:** every `δ = 1/3` poset with `n ≤ 5` has exactly
  `e(P) = 3` — tightness is realized only by rigid "three-extension" posets.
- **Duality** holds exactly in all 4320 non-chain posets (→ formalized in
  `Duality`).
- **Element deletion does not lift balanced pairs** (2640 failures) — an honest
  negative; the count is genuinely non-local (cf. the failed Frankl
  congruence-quotient reduction).
- **No local selection rule:** the most-balanced pair is always balanced (= the
  conjecture), but naive rules (first incomparable pair; both-minimal) fail ~31%
  of the time — the witness cannot be read off the Hasse diagram locally.

## Building

```sh
lake update && lake build         # fetches Mathlib v4.28.0 (cache) and builds
lake env lean scripts/axioms.lean # audit: only core axioms (+ the one headline sorry)
python3 research/explore.py       # reproduce the exploration
```

Pinned to `leanprover/lean4:v4.28.0` and Mathlib `v4.28.0`.

## References

Kislitsyn (1968); Fredman (1976); Linial (1984); Kahn–Saks (1984);
Brightwell–Felsner–Trotter (1995); Brightwell (1999, survey); Sah (2021). Full
citations in the repository [`references.md`](../../references.md#combinatorics).

## Status

Formalization of *known territory* plus two proved reductions (duality, twins).
The headline conjecture is open and kept as a single intentional `sorry`. The
duality and twin reductions are standard order-theoretic facts, formalized here
sorry-free; the computational `e(P)=3` extremal characterization is an
observation from the exhaustive `n ≤ 5` search.
