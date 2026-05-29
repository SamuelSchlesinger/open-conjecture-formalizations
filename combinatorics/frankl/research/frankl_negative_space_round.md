# Mining the negative space: degree-2 attacks and a structural reduction

After mapping what *doesn't* work, this round enumerated ideas aimed at the
identified gap and tested them.  Honest outcomes below.

## The diagnosis (what the negatives tell us)

Every barriered/failed method uses only **first-order (marginal / degree-1)**
information, or requires meet-control:

| Method | Why it fails |
|--------|--------------|
| entropy (iid; Gilmer–Sawin) | barriered at `(3−√5)/2 ≈ 0.38`; marginal/degree-1 |
| averaging (Reimer, Knill) | `log`-type bounds, never `½`; degree-1 |
| local witness-selectors | conjecture-equivalent (the non-locality finding) |
| elementary injections / Farkas | certify only `≤2`-set cases (= Sherali–Adams level 1) |
| topology (Möbius / homology) | separates easy/hard, blind to the final tight/slack cut |
| meet-control (modular/distributive) | needs a 2nd-order meet identity |

**Unifying reading:** the content lives in the **second-order (pairwise / degree-2)
correlation structure** that union-closure imposes globally; the coatom lemma
confirmed it from the other side (degree-1 buys exactly the coatoms; the wall is
the degree-2 balance `|U_i∩U_j| = |F|/4`).

## Ideas tried (script: `frankl_degree2_probe.py`)

Aimed at degree-2 / global structure.

- **(B) Second-moment inequality.**  Since `max_x mc_x ≥ Σmc_x²/Σmc_x` always,
  Frankl would follow from `I1 : Σmc_x² ≥ (|F|/2)Σmc_x` (`⟺ Σ|A∩B| ≥ (|F|/2)Σ|A|`).
  **`I1` is FALSE** — it fails (4 families at `m=4`, 63 at `m=5`, 293 at `m=6`),
  and *only on slack families* (`p_max > ½`).  On the boundary families it is
  exactly tight (`R=1`) — but only because those are precisely the every-half
  families, where tightness is automatic.  So the symmetric second moment is
  barriered just like averaging: tight where there is no slack, loose where one
  would need it.  **Negative.**
- **(C) Compression.**  The classic down-shift `S_{i←j}` **does not preserve
  union-closure** (576 violations at `m=4`, 127 432 at `m=5`).  This is the
  folklore reason union-closed families resist shifting.  **Negative.**
- **(E) Spectral.**  `λ_max(MᵀM)/|F| ≥ |F|/2` certifies a *shrinking* minority
  (27% → 7% → 0.6% over `m=3,4,5`).  Too weak.  **Negative.**

**Refinement of the map:** even degree-2, in its natural *symmetric-aggregate*
forms (`Σmc²`, spectrum, compression), is insufficient.  The needed structure is
*asymmetric / per-set*.  The Sherali–Adams/Lasserre level-2 idea, examined via
the FC-certificate gap (`fc_certificate_findings.md`), reduces to capturing the
**union-closure of the trace support** — an *order-`n`* constraint, which no
*fixed*-level LP/SDP hierarchy captures uniformly (level must grow with `n`).
So the hierarchy route is also barriered for the general conjecture.

## A structural reduction that DOES work (formalized)

Idea 4 — *structural induction rather than a local selector* — sidesteps the
non-locality wall and yields a clean, sorry-free, axiom-clean result
(`Frankl/LatticeProduct.lean`):

> **A Frankl witness lifts through products.**  If `j₁` is a join-irreducible of
> `L₁` with `2|↑j₁| ≤ |L₁|`, then `(j₁, ⊥)` is a join-irreducible of `L₁ × L₂`
> with `2|↑(j₁,⊥)| ≤ |L₁ × L₂|` (because `↑(j₁,⊥) ≃ ↑j₁ × L₂`).

Theorems: `supIrred_prod_bot`, `upSetProdEquiv`, `franklLattice_witness_prod_left`,
and `franklLattice_prod_left` (deriving `OrderBot L₂` from finiteness).

**Consequence.**  A nontrivial direct product is automatically a Frankl lattice,
so by induction on `Nat.card` the lattice form of the conjecture **reduces to the
directly-indecomposable lattices**.  Note this handles the Boolean lattices for
free (they are products of two-element chains) — consistent with the
`tight ⟺ Boolean` picture, where Boolean is the "easy" extreme.

This is a real narrowing of the problem obtained without any witness-selection,
which is exactly why the non-locality obstruction (every *local* selector is
conjecture-equivalent) does not apply to it.

## Workflow round 2: decomposition axes & fresh registers

A 10-idea multi-agent campaign (each idea investigated by a probe, then
adversarially verified by an independent skeptic that defaults to *refuted* when
it cannot confirm).  Honest outcomes:

**Confirmed (verified, high confidence):**
- **Geometric lattices** (atomistic + upper-semimodular = matroid flats): join-
  irreducibles are the atoms, and *every atom* `a` has `2|↑a| ≤ |L|` — 0 failures
  over 139 exhaustive + 1649 sampled + matroid lattices.  Frankl holds with any
  atom as witness (Reinhold's semimodular case; the atom rule is explicit).
  Formalizable, but needs a semimodular/geometric class not yet in Mathlib —
  *deferred*.
- **Vertical / ordinal-sum cut**: a cut element `c` gives `Frankl(↑c) ⟹ Frankl(L)`.
  **FORMALIZED**: `Frankl/LatticeCut.lean` (`franklLattice_witness_of_cut`,
  `supIrred_val_of_cut`, `upSetCutEquiv`), sorry-free, axiom-clean.
- **Twin-free reduction** (set form): deleting one of a pair of twin elements
  preserves union-closure, `|F|`, and lifts a Frankl element ⟹ reduces to
  separating families.  Exhaustive `k≤4`, 0 failures.  **FORMALIZED**:
  `Frankl/FamilyTwinFree.lean` (`franklConjectureFor_of_erase_twin`,
  `isUnionClosed_image_erase`, and supporting `injOn_erase_of_twin`,
  `card_image_erase_of_twin`, `memberCount_image_erase_of_twin`, …), sorry-free,
  axiom-clean.

**Partial:** Möbius `μ(⊥,⊤)=0 ⟹ a strict Frankl witness exists` (0 violations,
but this is the already-known *easy side* — `μ≠0` non-spheres also slack).
Subdirect-product lift: only the trivial-witness case survives.

**Refuted / failed (with explicit counterexamples, e.g. the `[0,1,2,3,7]`
closure system):** doubly-irreducible witness (M3 etc. have none), meet-
irreducible global counting (all aggregates break — barriered like averaging),
congruence-quotient reduction (no clean lift), and a conditioned descent-coupling
entropy retry on indecomposables (single-step descent gain evaporates by `k=4`,
stays below the `0.382` barrier).

**Net:** the conjecture's lattice form now reduces to lattices that are directly
indecomposable (`Frankl.LatticeProduct`) **and** vertically indecomposable
(`Frankl.LatticeCut`); geometric lattices are a fully-understood solved subclass.

## Reproduce

```sh
python3 research/frankl_degree2_probe.py
```
