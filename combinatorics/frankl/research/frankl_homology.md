# Full homology of the order complex: a sharper topological signal

Refining the Möbius (`μ`) probe (`lattice_frankl_attack.md`): instead of only the
Euler characteristic `μ(⊥,⊤)`, compute the **full reduced homology** of the order
complex `Δ((⊥,⊤))` (chains of the proper part), and relate the homotopy type to
Frankl-tightness.  Script: `frankl_homology_probe.py` (GF(2) Betti numbers;
**verified**: reduced Euler characteristic `=` `μ(⊥,⊤)` for all 2479 lattices in
`B_4`, so the homology code is correct).

## Findings (exhaustive on `B_4`, confirmed on sampled `[5]`)

**1. Tight ⟹ homotopy sphere.**  Every *tight* (extremal, `2·min_j|↑j| = |L|`)
lattice has order-complex reduced Betti vector among
`()`, `(1)=S⁰`, `(0,1)=S¹`, `(0,0,1)=S²`, … — a single `1` in top degree.  The
extremal lattices are exactly homotopy spheres, generalising the Boolean lattice
(whose proper part is a sphere).  This is a clean necessary condition not in the
literature (Bouchard arXiv:2503.00277 does not use topology).

**2. Non-spherical ⟹ strict slack (refines `μ=0 ⟹ slack`).**  If `Δ((⊥,⊤))` is
*not* a homotopy sphere — acyclic, or with higher/multiple reduced homology
(e.g. reduced Betti `(2,)`, `(1,1)`, `(0,2)`) — then Frankl holds with strict
slack.  This strictly extends the `μ=0` criterion: `μ=0` lattices are acyclic-or-
cancelling and were already "easy", but now `μ≠0`-but-non-spherical lattices
(like `(2,)`, `μ̃=2`) are also certified easy.  The only *hard candidates* are the
**spherical** lattices.

**3. The wall, at the finest resolution.**  Spherical does **not** imply tight:
in `B_4`, the 765 spherical lattices split into **97 tight and 668 slack** (e.g.
`S¹` appears as both).  So homology narrows the hard cases to "spheres" but the
*final* tight/slack distinction is **invisible to it**.

## Reading

Topology — even the full homology — behaves exactly as the non-locality synthesis
predicts.  It *sees* the structure (the easy cases are precisely the
non-spherical complexes; the extremal cases are spheres) and gives a strictly
sharper easy/hard separator than `μ`.  But the *decisive* cut — which homotopy
spheres are actually extremal — lives below the topological resolution, in the
same conjecture-equivalent core every register reaches.  The chain is now:

> non-atomistic ⟹ `μ=0` (crosscut, provable) ⟹ non-spherical possible …
> non-spherical ⟹ slack (sharper, empirical) ; hard candidates = spheres ;
> tight ⟺ ??? (within spheres — non-topological, = the conjecture).

## Reproduce

```sh
python3 research/frankl_homology_probe.py
```
