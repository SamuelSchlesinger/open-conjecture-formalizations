# Frankl Entropy-Transport Checklist

This checklist is the autonomous work queue for the Frankl project.  The goal
is to keep the thread pointed at the current frontier: verify the Gilmer/AHS
entropy hinge, isolate the coupled improvement mechanism, and migrate the
stable finite pieces into Lean.

## Current Frontier

- [x] Document the iid entropy barrier at `(3 - sqrt 5) / 2`.
- [x] Audit the Alweiss-Huang-Sellke one-variable hinge in executable form.
- [x] Identify the coupled replacement for the AHS product term: use
  Frechet-feasible zero-zero kernels `t`, not only history transports.
- [x] Formalize the one-coordinate coupled-OR algebra in Lean.
- [x] Add the formal global coupled-kernel certificate criterion needed to
  improve the constant toward `1 / 2`.  The actual existence theorem remains
  a hard theorem box below.

## Phase 1: Make the AHS Hinge Certifiable

- [x] Reproduce the `I1`, `I2`, and `I3` checks from the AHS appendix in
  `gilmer_ahs_verification.py`.
- [x] Replace high-precision floating checks with mpmath interval enclosures
  and conservative rational floors.
- [x] Emit a compact certificate file for the finite `I1` and `I2` tables.
- [x] Add a checker for the emitted AHS audit certificate payload.
- [x] Add the Lean rational finite-row checker and AHS rational floor data.
  The transcendental row-to-inequality proof remains a hard theorem box below.
- [x] Prove the rational positivity floor for the `I3` analytic tail margin
  in Lean.  The direct logarithmic inequality remains a hard theorem box
  below.
- [x] Record exactly which parts are copied from the literature and which
  are independently checked.

### AHS Provenance Notes

- Literature inputs from Alweiss-Huang-Sellke: the reduction to the
  one-variable hinge `phi * h(x^2) >= x * h(x)`, the intervals `I1`, `I2`,
  `I3`, the `L(x) = (1 - x^2)G''(x)` numerator, the `15.5` Lipschitz bound on
  `I1`, the `1/400` mesh radius, the monotone-chain method on `I2`, and the
  final analytic margin used on `I3`.
- Independently checked here: high-precision recomputation of every finite
  `I1` row, high-precision reconstruction of the `I2` chain and gaps,
  positivity of the `I3` margin, JSON payload consistency, and the
  one-coordinate coupled-OR/Frechet-kernel extension.
- Not yet independently certified: a Lean proof of the transcendental
  interval enclosures and a Lean proof that the certificate rows imply the AHS
  inequality.  The current JSON uses mpmath interval arithmetic and rational
  floors as the bridge format.

## Phase 2: Coupled One-Coordinate Theory

- [x] Prove algebraically that a marginal `p` can realize OR targets
  `q in [p, min(2p,1)]` by choosing intersection mass `r = 2p - q`.
- [x] Prove that every `1/4 <= p <= 1/2` coordinate can be centered at
  OR marginal `1/2`.
- [x] Promote the real-algebra statement to a finite probability statement
  about two Bernoulli coordinates with equal marginals.
- [x] Prove the entropy consequence: if `p < q < 1 - p`, then
  `h(q) > h(p)`.
- [x] Separate the rare-coordinate case `0 < p < 1/4`, where full centering is
  impossible but the target `q = 2p` still gains entropy.
- [x] Define the Frechet-kernel coupled hinge:
  choose `kappa` on histories and `t(x,y)` in the Frechet interval.

## Phase 3: Global Coupling and Obstruction Search

- [x] Test critical-coordinate centering on small union-closed families.
- [x] Implement assignment/column-generation checks for sampled misses.
- [x] Strip clone and coordinate-order faces before interpreting dual stress.
- [x] Add a certificate emitter and checker for successful column-generation
  runs.
- [x] Search for the smallest reduced/maximal family requiring more than one
  assignment column to center a critical set.  In a random reduced/maximal
  seven-coordinate scan with 400 generated families, no generated case
  appeared; all 10 reduced/maximal critical checks were sampled-feasible.
- [x] Search for a genuine obstruction to simultaneous centering.  None was
  found in the current exact/sampled/generated scans; future findings should
  be classified as coordinate-order, clone, trace-preserving, leakage, or new.
- [x] Generalize the arithmetic part of trace-preserving boosts into a
  symbolic Lean lemma.  The remaining combinatorial matching construction is
  still a future formalization target.
- [x] Add the formal accounting slot for total-correlation cost.  The
  remaining hard theorem is to bound this cost for a genuinely global
  coupling.

## Phase 4: Three-Coordinate Frontier Closure

- [x] Close the size-17 frontier by zero-fiber shadow certificates.
- [x] Verify that the propagation scan has no remaining frontier through
  size 18.
- [x] Extract the unique-top symbolic propagation proposition.
- [x] Turn the zero-fiber shadow certificate into a Lean-friendly finite
  data statement.
- [x] Formalize the Horn propagation lemmas over trace fibers.
- [x] Formalize the arithmetic case-split core of the unique-top symbolic
  propagation proposition.  The remaining trace-fiber instantiation is covered
  by the hard theorem list below.
- [x] Decide whether the remaining template scan can be proved parametrically
  or should remain a finite certificate.

Decision: keep the remaining template scan as a finite certificate for now.
The unique-top class has a symbolic proof target, but the other support
templates have enough case structure that forcing a premature parametric proof
would likely hide the actual obstruction geometry.

### Current Hard Theorem Boxes

These are not merely engineering tasks; they are the current mathematical
frontier of the approach.

- Global coupled-kernel theorem: prove enough compatible Frechet kernels exist
  to improve the constant toward `1 / 2`.
- AHS Lean transcendental certification: replace the mpmath interval payload
  by Lean-checked logarithmic interval enclosures.
- AHS row-to-inequality proof: connect the rational table checker to the
  analytic lemmas over `I1`, `I2`, and `I3`.
- Shadow checker: prove the size-17 `FrontierData` records really satisfy all
  relaxed shadow join constraints, rather than only recording the payload.
- Unique-top trace-fiber instantiation: connect the checked `TraceProfile5`
  theorem to trace fibers extracted directly from an arbitrary projected
  union-closed family.
- Global total-correlation bound: prove the formal `totalCorrelationCost`
  accounting term is smaller than the raw Frechet-kernel entropy gain in a
  nontrivial class.

## Phase 5: Lean Migration Order

- [x] `Frankl.Basic`: singleton-containing case.
- [x] `Frankl.Fiber`: maximum-member and Horn propagation lemmas.
- [x] `Frankl.CoupledOr`: one-coordinate coupled-OR algebra.
- [x] `Frankl.Split`: define `L_i`, `R_i`, and prove the Frankl witness
  equivalence `|L_i| <= |R_i|`.
- [x] `Frankl.Trace`: define trace fibers and support joins.
- [x] `Frankl.Probability`: finite distributions, Bernoulli coordinate
  marginals, and two-coordinate couplings.
- [x] `Frankl.Entropy`: binary entropy and monotonicity around `1/2`.
- [x] `Frankl.EntropyGain`: rational finite certificate format for
  coordinate-gain versus total-correlation accounting.
- [x] `Frankl.TotalCorrelation`: finite Boolean laws and the
  total-correlation chain identity.
- [x] `Frankl.Certificates`: finite certificate checker for AHS and frontier
  tables.
- [x] `Frankl.AHSInterval`: interval-row, Lipschitz, and monotone-chain
  interfaces for the AHS certificate.
- [x] `Frankl.GlobalCoupling`: uniform global couplings and coordinate OR
  center predicates.

## Session Startup Commands

Run these before serious autonomous work:

```sh
git status --short
python3 -m py_compile combinatorics/frankl/research/gilmer_ahs_verification.py combinatorics/frankl/research/window_experiment.py
python3 combinatorics/frankl/research/gilmer_ahs_verification.py --verify-ahs --one-coordinate-frontier --coupled-coordinate-probe
(cd combinatorics/frankl && lake build)
```

Expected caveats:

- `Frankl/Conjecture.lean` currently contains the project-level open
  conjecture statement and uses `sorry`.
- `graph-theory/reconstruction-conjecture` may be dirty from unrelated work;
  ignore it unless the user asks otherwise.

## Immediate Next Bite

- [x] Build `Frankl.Split` and prove the split-family counting equivalence.
- [x] Build `Frankl.Probability` just far enough to restate
  `Frankl.CoupledOr` as a finite coupling theorem.
- [x] Build `Frankl.Entropy` with binary entropy symmetry and monotonicity on
  the left side of `1 / 2`.
- [x] In parallel, make `gilmer_ahs_verification.py` emit rational interval
  rows for `I1` and `I2`.
- [x] Build the first `Frankl.Certificates` checker for
  `ahs_hinge_certificate.json`.

## Phase 6: AHS Lean Certification Expansion

Goal: turn the current AHS audit payload into a Lean-verifiable certificate
chain.  The first pass should avoid proving all transcendental facts at once;
instead, make each missing bridge explicit.

- [x] Add `Frankl.AHSFormula` defining the AHS functions `G`, `L`, `g1`, and
  `g2` using `Real.binEntropy` and `Real.log`.
- [x] Prove that the local `G` agrees with
  `phi * h (x^2) - x * h x` on `0 < x < 1`.
- [ ] Prove the algebraic identity connecting `L(x)` with
  `(1 - x^2) * deriv^[2] G x`, assuming the differentiability side
  conditions.
- [x] Add a Lean representation of an AHS interval row:
  rational endpoint, rational lower floor, and statement that a function is
  bounded below on that row's interval.
- [x] Add a theorem saying the `I1` row lower bounds plus the Lipschitz bound
  imply `G >= 0` on `I1`.
- [x] Add a theorem saying the `I2` monotone-chain rows imply `g1 >= g2` on
  `I2`, assuming the monotonicity hypotheses used by AHS.
- [x] Add a theorem statement for the `I3` analytic tail reduction, with the
  current rational positive margin as an input hypothesis.
- [x] Decide whether to prove log interval bounds directly in Lean or generate
  a trusted-by-kernel rational Taylor certificate.
- [ ] If using Taylor certificates, make the generator emit coefficients,
  remainder bounds, and domain side conditions.
- [x] Produce one tiny end-to-end Lean certificate row for a toy interval
  before scaling to the full AHS table.

Done means: Lean has theorem statements, data structures, and at least one
nontrivial checked row proving a lower-bound implication without relying on
Python at proof time.

Decision: use rational Taylor certificates for logarithmic bounds.  Direct
Lean proofs of all log interval enclosures would obscure the finite-certificate
shape; Taylor rows can expose coefficients, remainder bounds, and domain
conditions as kernel-checkable rational inequalities.

## Phase 7: Frontier Shadow Checker

Goal: convert `Frankl.FrontierData` from recorded payload into a verified
finite checker for the size-17 shadow certificates.

- [x] Define bitmask membership for trace masks `0..7` in Lean.
- [x] Define `maskUnion : Nat -> Nat -> Nat` for three-bit trace masks and
  prove it agrees with set union under the bit interpretation.
- [x] Define `shadowSupportUnionClosed` in Lean and check every recorded
  zero-shadow support.
- [x] Define zero-invariance of a fiber shadow under union with the zero
  shadow.
- [x] Define `shadowsJoinInto` for two source shadows and one target shadow.
- [x] Check every `fiberShadows` entry in `size17FrontierShadowRecords`.
- [x] Prove that the recorded `forcedZeroCoordMax` is at least half of the
  recorded `totalSize`.
- [x] Prove that every recorded count vector has total size `17`.
- [x] Add a theorem bundling the four records into a single
  `size17FrontierShadowRecordsValid` statement.
- [x] Replace any `native_decide` proof over large data with a transparent
  `decide` proof if it remains fast enough.

Done means: the size-17 frontier records are not just stored in Lean; Lean
checks the same finite predicates that the Python shadow routine checks.

## Phase 8: Full Unique-Top Formalization

Goal: upgrade `Frankl.UniqueTop` from arithmetic case split to the actual
trace-fiber theorem.

- [x] Define a `TraceProfile5` structure for fibers `A`, `B`, `C`, `D`, `T`
  with their trace-join relations.
- [x] State the singleton-top hypothesis as `T.card = 1`.
- [x] Define the hit count of a hidden coordinate over a fiber.
- [x] Prove that if a trace fiber is singleton and contains a maximum member,
  then all unions landing in it equal that member.
- [x] Prove the `allB` case: if all members of `B` contain `h`, total hits
  are at least `r + b + 3`.
- [x] Prove the `not allB` case: one `B` member omitting `h` forces all of
  `C` and all of `D` to contain `h`.
- [x] Connect the two cases to
  `uniqueTop_symbolicPropagation_bound`.
- [x] Instantiate the theorem on the parametric obstruction count vector
  from the note.
- [x] Prove the final parametric arithmetic inequality showing the hidden
  coordinate is a Frankl witness.

Done means: the proposition named “Unique-top symbolic propagation” in the
LaTeX note has a Lean theorem with the same mathematical hypotheses.

## Phase 9: Coupled-Kernel Global Program

Goal: find and formalize a class where compatible Frechet kernels exist and
the entropy gain beats the dependence cost.

- [x] Define finite global couplings on a family `F` as probability weights on
  `F × F` with uniform marginals.
- [x] Define coordinate OR marginals for a global coupling and prove they
  specialize to `TwoBernoulliCoupling.orMarginal` per coordinate.
- [x] Define the center polytope of critical coordinates in Lean.
- [ ] Prove the exact permutation-coupling reduction for uniform finite
  couplings using Birkhoff-von Neumann as a theorem assumption first.
- [ ] Add a finite theorem: if `1/2` lies in the convex hull of permutation
  OR vectors, then critical coordinates have positive coordinate entropy
  gain.
- [x] Formalize coordinate-order faces `i <= j` and prove `q_i <= q_j` for
  every coupling.
- [ ] Prove clone quotienting preserves the existence of a Frankl witness.
- [ ] Prove the one-positive trace-preserving matching construction currently
  used by the Python stress test.
- [ ] Search for a natural nontrivial family class where the global center
  polytope is provably nonempty.
- [ ] If a class is found, add it as a theorem target before attempting the
  full conjecture.

Done means: at least one nontrivial class has a fully stated and partially
proved coupled-kernel theorem, or a precise obstruction certificate explains
why the class fails.

## Phase 10: Total-Correlation Accounting

Goal: turn the placeholder `totalCorrelationCost` into a computable or
bounded quantity.

- [x] Define total correlation for finite Boolean vectors using Mathlib's
  finite sums and `Real.binEntropy`.
- [x] Prove the chain identity
  `H(Z) = sum_i h(q_i) - TC(Z)` for a finite Boolean law, initially as a
  theorem statement with supporting definitions.
- [x] Implement a Python exact evaluator for total correlation of a
  permutation coupling on small families.
- [ ] Compare raw coordinate entropy gain and total-correlation growth for
  all exact `n <= 4` critical-center cases.
  Partial run completed for `n <= 4`, `max_exact_size = 7`: centered
  permutations exist, but the best centered permutation seen still has
  negative net entropy gain because total-correlation growth dominates the
  raw coordinate gain.  The full `max_exact_size = 8` pass is heavier and
  remains to be optimized or run as a longer campaign.
- [ ] Emit JSON witnesses where coordinate gain beats total-correlation cost.
- [x] Emit JSON counter-witnesses where centering works but total correlation
  consumes the gain.
- [ ] Identify whether the hard cases correlate with clone/order faces,
  trace-preserving boosts, or leakage.
- [x] Add a Lean structure for a finite entropy-gain certificate:
  coordinate gains, TC bound, and positive net margin.

Done means: the phrase “total-correlation cost” is no longer qualitative; it
has definitions, exact small-family data, and at least one certificate format.

## Phase 11: Experimental Campaigns

Goal: keep computational exploration reproducible and aimed at theorem
formation.

- [x] Add `--campaign` presets to `window_experiment.py` for the standard
  scans used in the note.
- [ ] Add JSON summaries for exhaustive `n=4` critical subset scans.
- [ ] Add JSON summaries for reduced/maximal random `n=6`, `n=7`, and `n=8`
  scans.
- [x] Add a checker for campaign JSON summaries.
- [ ] Search specifically for generated-feasible cases needing at least two
  assignment columns.
- [ ] Search specifically for reduced/maximal cases with two or more critical
  coordinates.
- [ ] Search for remaining-cone directions where trace-preserving positive
  assignment fails but controlled leakage succeeds.
- [ ] Store the smallest example of each phenomenon in `research/examples/`.
- [x] Add a short README in `research/examples/` explaining each example's
  mathematical role.

Done means: future sessions can rerun the computational evidence without
remembering bespoke command lines.

## Phase 12: Paper/Lean Synchronization

Goal: keep the LaTeX note, scripts, and Lean project from drifting apart.

- [x] Add a “Lean status” table to the LaTeX note listing each theorem and
  its corresponding Lean file.
- [x] Add a “Script status” table listing each JSON artifact and the command
  that regenerates/checks it.
- [x] Add citations for Gilmer and Alweiss-Huang-Sellke to `references.md`.
- [x] Update `README.md` with the new artifact files and verification
  commands.
- [x] Add a CI-friendly script that runs the lightweight checks:
  Python compile, AHS certificate check, center certificate check, and
  `lake build`.
- [x] Add a note warning that mpmath interval payloads are audit artifacts,
  not kernel-checked transcendental proofs.

Done means: a new contributor can tell which parts are proved, audited,
experimental, or conjectural without reading the whole thread.

## New Immediate Next Bite

- [x] Build `Frankl.AHSFormula` with definitions of `phi`, `G`, `L`, `g1`,
  and `g2`.
- [x] Build Lean bitmask utilities for `FrontierData`.
- [x] Add `--campaign` presets to `window_experiment.py`.
- [x] Add `research/examples/` and store the smallest generated-feasible
  center certificate case.
- [x] Add the LaTeX/Lean status table to the note.
