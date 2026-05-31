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
the **parallel composition `P ⊕ P`**; and **width ≤ 1 ⇔ chain**. Stated precisely
but **not** formalized (known hard
theorems): Linial's width-2 theorem, and the constant bounds (Kahn–Saks `3/11`,
BFT `(5−√5)/10`). The full conjecture remains the single `sorry`.

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
