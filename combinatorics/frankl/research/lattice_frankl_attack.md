# A lattice-side attack on Frankl's conjecture — ideas, tests, and honest limits

Open-frontier attempt (2026-05-28).  Working in the **lattice form** (proved
equivalent to the set conjecture in `Frankl.Lattice` / `Frankl.LatticeReverse`):

> Every finite lattice `L` with `|L| ≥ 2` has a join-irreducible `j` with
> `|↑j| ≤ |L|/2`, where `↑j = {x : j ≤ x}`.

**This did not solve the conjecture** (it is open, and the entropy method is
barriered at `(3−√5)/2`).  What follows is a genuine attempt: ideas, the ones
that died, one verified new sufficient condition, and a strengthened condition
that survives all testing but which I explicitly do **not** claim to be true.

## Ideas enumerated

1. **Uniform averaging over join-irreducibles.**  If `avg_j |↑j| ≤ |L|/2` then
   `min ≤ avg` proves it.  **Dead:** the lattice `⊥ < a < {b₁,b₂} < ⊤` has
   `Σ_j |↑j| = 8 > 7.5 = |J|·|L|/2`.  The *deep* join-irreducible `a`
   (`|↑a| = 4`) inflates the average; Frankl holds only via the *shallow*
   (maximal) join-irreducibles `b₁,b₂`.

2. **Reduction to maximal join-irreducibles.**  `|↑j|` is monotone decreasing in
   `j`, so the minimum is attained at *maximal* join-irreducibles.  Hence
   Frankl ⟺ some maximal join-irreducible has `|↑j| ≤ |L|/2`.  Averaging is
   doomed precisely because deep join-irreducibles are not candidates.

3. **Weight method** = Poonen's theorem; known insufficient in general
   (FC-family theory).  **Entropy method** — barriered; paused by request.

4. **Coatom with a large ideal (NEW, verified).**  For a coatom `m` and a
   join-irreducible `x ⊄ m` (one exists since `⊤` is a join of
   join-irreducibles), `↑x ⊆ L ∖ ↓m` because `α ≥ x` and `α ≤ m` would give
   `x ≤ m`.  So if `|↓m| ≥ |L|/2` then `|↑x| ≤ |L| − |↓m| ≤ |L|/2`.
   Formalized: `Frankl.franklLattice_of_large_coatom_ideal`.  Incomparable to
   the modular case (it handles non-modular lattices with a big coatom-ideal;
   misses balanced modular lattices like `M₃`).

5. **Engine + strengthened coatom-union condition.**  Generalizing 4: *any*
   finset `T` disjoint from `↑x` with `|T| ≥ |↑x|` certifies the join-irreducible
   `x` (formalized: `Frankl.two_mul_card_upset_le_of_disjoint_finset`).  Taking
   `T = ⋃_{coatoms m ⊉ x} ↓m` gives the criterion:

   > (★) ∃ join-irreducible `x` with `|⋃_{coatoms m ⊉ x} ↓m| ≥ |↑x|`.

   This is a *sound sufficient condition* (it implies Frankl via the engine).

## Computational evidence for (★)

`lattice_frankl_attack.py` checks (★):

| family | lattices | Frankl fails | (★) fails |
|--------|----------|--------------|-----------|
| all closure systems on `[3]` (`B₃`) | 60 | 0 | **0** |
| all closure systems on `[4]` (`B₄`) | 2479 | 0 | **0** |
| sampled closure systems on `[5]` | ~4000 (to size 28) | 0 | **0** |
| sampled closure systems on `[6]` | 3000 (to size 40) | 0 | **0** |
| partition lattices `Π₃, Π₄, Π₅` | sizes 5, 15, 52 | 0 | 0 (slack > 0) |
| subspace lattice of `𝔽₂³` | 16 | 0 | 0 (slack > 0) |

(For comparison, conditions {modular, large-coatom-ideal, large-atom-filter}
leave **26** escapers in `B₄`, dropping to 22 after adding "join-irreducible
coatom".  Condition (★) leaves none anywhere tested.)

## Honest assessment

(★) is striking — zero failures across everything tested, including the
classically hard partition lattices.  **But this is not a proof, and I do not
believe it proves Frankl.**  Reasons:

- A sound sufficient condition that *never* failed would solve a 45-year-old
  open problem; the overwhelmingly likely explanations are (a) my lattice
  samples are biased toward "nice" structures (closure systems on small ground
  sets, geometric/modular lattices), or (b) deciding whether (★) always holds is
  itself equivalent in difficulty to the conjecture.
- The gap `L∖↑x ∖ ⋃↓m` (elements not above `x` but below only `x`-containing
  coatoms) can be nonempty; nothing I have rules out a sporadic lattice where it
  swallows the slack for *every* join-irreducible `x`.

So the rigorous deliverables are the **engine** and the **large-coatom-ideal**
theorem (both in `Frankl.Lattice`, sorry-free, axiom-clean).  Condition (★) is
recorded as an intriguing, empirically-robust, *unproven* line — a good target
for an adversarial search over non-closure-system lattices, which is the honest
next step rather than a claimed proof.

## Reproduce

```sh
python3 research/lattice_frankl_attack.py
```
