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

## Reproduce

```sh
python3 research/frankl_degree2_probe.py
```
