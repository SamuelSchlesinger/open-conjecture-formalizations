# Frankl's Union-Closed Sets Conjecture

A Lean 4 formalization scaffold for Frankl's union-closed sets conjecture.

## The Conjecture

For every finite nontrivial union-closed family of finite sets, some element
belongs to at least half of the member-sets.

In Lean, a family is represented as `Finset (Finset α)`, and the half-bound is
written without division:

`F.card ≤ 2 * memberCount x F`

## Current Formalized Territory

The project proves the classical small-set cases and several local pieces of
the (now-paused) entropy-transport attack.

- **Singleton case.** If a union-closed family contains `{x}`, then the map
  `A ↦ insert x A` injects the member-sets omitting `x` into the member-sets
  containing `x`; hence `x` occurs in at least half the family.
- **Doubleton case.** If a union-closed family contains `{a, b}` with `a ≠ b`,
  then `a` or `b` occurs in at least half the family.  Partition the family by
  the membership pattern of `a` and `b`; the map `A ↦ insert a (insert b A)`
  injects the `(a∉, b∉)` block into the `(a∈, b∈)` block, and a short counting
  argument shows `a` or `b` must be abundant
  (`Frankl.isFranklElement_left_or_right_of_pair_mem`).

These are the standard "a member-set of size ≤ 2 forces the conjecture" results
(Bruhn–Schaudt survey); they are formalized as known territory, independent of
the entropy program.

### Lattice (Poonen) reformulation

`Frankl.Lattice` states the equivalent lattice form (Poonen 1992): every finite
lattice `L` with `|L| ≥ 2` has a join-irreducible element `j` (Mathlib's
`SupIrred`) below at most half of the elements, `2 * |{x : j ≤ x}| ≤ |L|`
(`FranklLattice`).  Two known classes are proved completely and sorry-free:

- **Distributive lattices** (`franklLattice_of_distribLattice`), by an elementary
  Birkhoff-free argument: a maximal join-irreducible `j` with the map
  `x ↦ ⨆ {y ≤ x : ¬ j ≤ y}` injects the up-set of `j` into its complement.
  Finite chains follow (`franklLattice_of_linearOrder`).
- **Lattices with a left-modular coatom** (`franklLattice_of_leftModular_coatom`,
  Woodroofe) — the "master" case covering modular, dually (lower) semimodular,
  and supersolvable lattices.  Pick a join-irreducible `x ⊄ m`; since the coatom
  `m` satisfies `x ⊔ m = ⊤`, the map `α ↦ m ⊓ α` injects `↑x` into its
  complement (injective by left-modularity `x ⊔ m ⊓ α = (x ⊔ m) ⊓ α`).
- **Modular lattices** (`franklLattice_of_modular`, Abe–Nakano) follow as a
  corollary: every element of a modular lattice is left-modular, and a finite
  nontrivial lattice has a coatom.  This strictly generalises the distributive
  case.
- **Large-coatom-ideal lattices** (`franklLattice_of_large_coatom_ideal`), found
  while attacking the open frontier: if some coatom `m` lies above at least half
  the elements then any join-irreducible `x ⊄ m` satisfies `↑x ⊆ L ∖ ↓m`, so
  `|↑x| ≤ |L|/2`.  No modularity needed; incomparable to the modular case.  Its
  engine `two_mul_card_upset_le_of_disjoint_finset` (any finset disjoint from
  `↑x` of size `≥ |↑x|` certifies `x`) underlies the experimental condition (★)
  explored in `research/lattice_frankl_attack.md` — which survives all testing
  but is **not** a proof.

**Poonen's equivalence is fully proved**: `franklConjecture_iff_franklLattice`
shows `FranklConjecture ↔ FranklLattice` (sorry-free, axiom-clean).

- *Forward* (`franklConjecture_imp_franklLattice`): given a finite lattice `L`,
  the members `f a = {j join-irreducible : ¬ j ≤ a}` (`a ∈ L`) form a union-closed
  family on the join-irreducibles whose Frankl element is a join-irreducible `j₀`
  with `2 |↑j₀| ≤ |L|`.
- *Reverse* (`franklLattice_imp_franklConjecture`, in `Frankl.LatticeReverse`):
  given a union-closed family `F` (with `∅ ∈ F`), the poset `(F, ⊆)` is a finite
  lattice; a meet-irreducible `m` has a least strict upper bound `m⁺`, and any
  `x ∈ m⁺ ∖ m` makes `m` the largest `x`-free member, so `↓m` is exactly the
  `x`-free members.  The dual lattice bound `2 |↓m| ≤ |F|` then makes `x`
  abundant.  Supporting results: `InfIrred.exists_least_gt` (a meet-irreducible
  in a finite lattice has a unique upper cover) and `ucLattice` (the lattice
  structure on a union-closed family).

The meet-irreducible (dual) form `FranklLatticeMeet` — the formulation Poonen
proved equivalent to the conjecture — is shown equivalent to `FranklLattice` by
order duality (`franklLattice_iff_franklLatticeMeet`).  The
semimodular/modular/geometric lattice cases are future work.

**Reduction to indecomposables** (`Frankl.LatticeProduct`): a join-irreducible
witness in one factor lifts to a product — if `2|↑j₁| ≤ |L₁|` then
`2|↑(j₁,⊥)| ≤ |L₁ × L₂|`, since `↑(j₁,⊥) ≃ ↑j₁ × L₂`
(`franklLattice_witness_prod_left`, `franklLattice_prod_left`).  Hence a
nontrivial direct product is automatically a Frankl lattice, and by induction on
`Nat.card` the conjecture **reduces to the directly-indecomposable lattices**
(Boolean lattices, being products of two-element chains, are handled for free).
This is a structural reduction, obtained without any local witness-selection —
see `research/frankl_negative_space_round.md`.

### Extremal / balanced families (`Frankl.Coatom`)

A self-contained study of **every-half** families — union-closed families in
which every ground element lies in exactly half the member-sets
(`2 * memberCount x F = |F|`), the set-side image of the *Frankl-extremal* case
(see `research/frankl_tight_boolean.md`).  All sorry-free and axiom-clean.

- **Coatom lemma** (`coatom_mem_of_everyHalf_twinFree`): a *twin-free*
  every-half union-closed family contains every coatom `(familyUnion F).erase i`.
  The member-subfamilies `{A ∈ F : i ∈ A}` are distinct (twin-free) and all of
  size `|F|/2` (every-half), hence pairwise incomparable; so for `i ≠ j` some
  member separates them, and the union of all `i`-avoiding members is exactly
  `U ∖ {i}`.  Supporting: `biUnion_id_mem_of_nonempty_subset` and the
  incomparability lemma `exists_mem_of_everyHalf_twinFree`.
- **Field-of-sets characterization** (`everyHalf_field_iff_powerset`): a nonempty
  twin-free family that is **both** union- and intersection-closed and every-half
  is exactly the full power set `(familyUnion F).powerset`.  Forward direction is
  the coatom-lemma payoff (intersection-closure generates every subset from the
  coatoms); the reverse (`isEveryHalf_powerset` &c.) shows the power set realizes
  all hypotheses, so Frankl's `½` bound is **sharp** — attained with equality at
  every element.  Dropping intersection-closure is exactly the open,
  conjecture-equivalent residual.

The active research program is tracked in `research/checklist.md`.  It focuses
on formalizing the Gilmer/AHS entropy hinge, testing a coupled-OR replacement,
and migrating stable finite certificates into Lean.

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `Frankl.Defs` | Finite families, union-closedness, member counts, conjecture statements | 0 |
| `Frankl.Basic` | Membership lemmas and the singleton + doubleton cases | 0 |
| `Frankl.Split` | Coordinate split families and the fixed-coordinate counting equivalence | 0 |
| `Frankl.Trace` | Trace fibers and induced union-closed trace supports | 0 |
| `Frankl.Fiber` | Maximum-member, fiber, and Horn propagation lemmas | 0 |
| `Frankl.CoupledOr` | One-coordinate coupled-OR algebra | 0 |
| `Frankl.Probability` | Four-atom Bernoulli couplings and realized OR targets | 0 |
| `Frankl.Entropy` | Binary entropy symmetry and monotonicity facts | 0 |
| `Frankl.EntropyGain` | Rational finite certificates for coordinate gain beating TC cost | 0 |
| `Frankl.TotalCorrelation` | Finite Boolean laws and total-correlation identity | 0 |
| `Frankl.CoupledHinge` | Finite Frechet-kernel hinge data and entropy gain | 0 |
| `Frankl.GlobalCoupling` | Uniform global couplings and coordinate OR center predicates | 0 |
| `Frankl.Certificates` | Generic rational lower-bound table checker | 0 |
| `Frankl.AHSFormula` | Lean definitions of the AHS hinge functions | 0 |
| `Frankl.AHSData` | Rational floors extracted from the AHS hinge certificate | 0 |
| `Frankl.AHSInterval` | Interval, Lipschitz, and monotone-chain interfaces for the AHS certificate | 0 |
| `Frankl.FrontierData` | Lean-friendly finite data for size-17 shadow certificates | 0 |
| `Frankl.Boost` | Arithmetic core of trace-preserving boost certificates | 0 |
| `Frankl.UniqueTop` | Arithmetic core of the unique-top propagation bound | 0 |
| `Frankl.SmallCases` | Empty and one-member family sanity checks | 0 |
| `Frankl.Lattice` | Lattice (Poonen) form; distributive/chain/modular cases; `Conjecture → Lattice`; dual form | 0 |
| `Frankl.LatticeReverse` | `Lattice → Conjecture`; full equivalence `Conjecture ↔ Lattice` | 0 |
| `Frankl.Conjecture` | Main open global statement and expanded form | 1 |

## Building

```sh
lake update && lake build
```

The top-level open conjecture file intentionally contains one `sorry`; all
supporting modules listed above are closed.

## Research Artifacts

| Artifact | Role |
|----------|------|
| `research/entropy_transport_strategy.tex` | English proof notebook for the entropy-transport program |
| `research/ahs_hinge_certificate.json` | mpmath interval audit payload for the Gilmer/AHS hinge |
| `research/center_generation_certificate.json` | sampled critical-centering misses resolved by assignment-column generation |
| `research/reduced_maximal_center_generation_certificate.json` | reduced/maximal random scan certificate payload |
| `research/tc_exact_n4_size7_summary.json` | bounded exact total-correlation accounting for small critical-center cases |
| `research/examples/generated_feasible_size11.json` | smallest stored generated-feasible centering example |
| `research/examples/tc_centered_cost_dominates_size6.json` | centered permutation where TC growth dominates raw coordinate gain |
| `research/checklist.md` | autonomous work queue and hard theorem boxes |

## Lightweight Verification

```sh
python3 -m py_compile research/gilmer_ahs_verification.py research/window_experiment.py
python3 research/gilmer_ahs_verification.py --check-ahs-certificate research/ahs_hinge_certificate.json
python3 research/window_experiment.py --check-center-certificate research/center_generation_certificate.json
python3 research/window_experiment.py --check-tc-summary research/tc_exact_n4_size7_summary.json
python3 research/window_experiment.py --campaign frontier-shadow
lake build
```

Named computational campaigns can be listed with:

```sh
python3 research/window_experiment.py --list-campaigns
```

The same lightweight suite is available as:

```sh
research/lightweight_checks.sh
```
