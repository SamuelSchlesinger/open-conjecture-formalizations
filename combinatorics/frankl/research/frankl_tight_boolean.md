# Conjecture: a Frankl-tight lattice is Boolean (partial proof)

Surfaced by the homology probe (`frankl_homology.md`): the *tight* lattices
(Frankl-extremal, `min_j |↑j| = |L|/2`) are exactly the homotopy spheres, and the
sphere dimensions match the Boolean sizes.  Sharpening:

> **Conjecture (lattice-form extremal characterization).**  A finite lattice `L`
> satisfies `min over join-irreducibles j of |↑j| = |L|/2` **iff** `L` is Boolean.

(`Boolean ⟹ tight` is easy: in `B_n` the join-irreducibles are the atoms, each
with `|↑a| = 2^{n-1} = |L|/2`.)  Then "Boolean proper part `≃` sphere" (classical)
recovers the homology finding.

**This is NOT a theorem — it is a strongly-supported conjecture with a partial
proof.**  Honest status below.

## Independence from Frankl

"Tight" means `min = |L|/2` *exactly*.  A hypothetical Frankl counterexample has
`min > |L|/2` and is therefore *not* tight, so this conjecture says nothing about
it — it does not imply Frankl.  Consequently any *proof* must use the equality
essentially: an argument using only "every join-irreducible has `|↑j| ≥ |L|/2`"
would force `min = |L|/2` and hence prove Frankl.

## Verification

- `B_4` exhaustive (all lattices with ≤ 4 meet-irreducibles): 97 tight, **all
  Boolean**; 0 Boolean-but-not-tight.
- ~45 000 tight lattices sampled across closure systems on `[5]…[8]` (to
  `|L| = 32`): **zero** non-Boolean.
- *Caveat:* random closure-system sampling is biased toward "nice" lattices; the
  literature notes exotic *set-form* extremal families (Renaud–Fitina,
  "Hungarian"), so residual doubt remains that a rare exotic lattice-form
  counterexample exists.

## Proof skeleton (2 of 4 steps proved)

```
tight ──(A)──▶ all-half ──(B)──▶ distributive ──┐
                  │ (proved)                      │ Birkhoff (D, proved)
                  ▼ ji-are-atoms ──────────────── ▶ Boolean
```

- **(proved) all-half ⟹ ji-are-atoms.**  `all-half` = every join-irreducible
  `j` has `|↑j| = |L|/2`.  If some join-irreducible `j` were not an atom, an atom
  `a < j` (also join-irreducible) would have `↑a ⊋ ↑j`, so
  `|↑a| > |↑j| = |L|/2`, contradicting `all-half`.  Hence every join-irreducible
  is an atom (the lattice is atomistic with `J(L)` an antichain).
- **(proved) distributive + `J(L)` an antichain ⟹ Boolean.**  Birkhoff: a finite
  distributive lattice is the lattice of down-sets of its join-irreducible poset
  `J(L)`; the down-sets of an antichain are *all* its subsets, i.e. a Boolean
  lattice.
- **(CRUX A, open) tight ⟹ all-half.**  Need: no join-irreducible has
  `|↑j| > |L|/2`.  Must use the equality (see Independence above).  *Open.*
- **(CRUX B, open) all-half ⟹ distributive.**  `all-half` constrains only first
  moments (each atom below exactly half the elements); distributivity is a
  second-moment/independence condition.  Marginals-at-`½` do not force
  independence in general — only the lattice axioms could, and the argument is
  not apparent.  Verified empirically (19 518 all-half lattices, 0
  non-distributive).  *Open.*

## Reading

This is the first genuinely *non-conjecture-equivalent* target the campaign
produced (it characterizes the equality case without resolving Frankl).  Two of
four steps are clean; the two crux steps are where the real content sits, and
both have identified, non-trivial obstructions.  A complete proof would be a
genuine new theorem (lattice-form extremal characterization), apparently absent
from the literature (Bouchard arXiv:2503.00277 uses no topology; Das–Wu
arXiv:2412.03862 study the *set*-form equality, which has more extremal families).

## Reproduce

```sh
python3 research/frankl_tight_boolean.py
```
