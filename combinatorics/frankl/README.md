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
