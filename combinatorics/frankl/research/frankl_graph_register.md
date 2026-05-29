# The graph register: exploring Frankl via maximal independent sets

A genuinely new register for the open-frontier campaign (one I had never touched):
the **graph formulation** of Frankl (Bruhn–Charbit–Schaudt–Telle, 2015).

> Frankl ⟺ every finite graph with an edge has two **adjacent** vertices each in
> at most half of its maximal independent (stable) sets.

Trivial for non-bipartite graphs; the hard core is **bipartite** graphs.  Script:
`frankl_graph_probe.py`.

## Findings

**Verification.** The conjecture holds on all 33 853 graphs with an edge on
`n ≤ 6` vertices (zero failures), bipartite included.

**A clean reframing (derived here).** Adjacent vertices never lie in the same
maximal independent set, so for any edge `uv`, `freq(u)+freq(v) ≤ |MIS|`.
Therefore at most one endpoint of any edge is **heavy** (in `>` half the MIS),
i.e. *heavy vertices are pairwise non-adjacent* — an independent set.  An
independent set that is also a vertex cover forces the graph to be bipartite
with that set as one side.  Hence:

> **The conjecture fails for `G` iff `G` is bipartite and some bipartition side
> is *entirely* heavy** (every vertex of that side in `>` half the MIS).

**A clean provable fragment.** If `G` has a *triangle* `{a,b,c}`, then
`freq(a)+freq(b)+freq(c) ≤ |MIS|` (at most one per MIS), so at least two of them
are light — and they are adjacent.  This is exactly why non-bipartite graphs are
easy.

**An honest negative.** Heavy ≈ low-degree, suggesting "an edge between two
high-degree vertices has both light".  The degree-sum rule (pick the edge
maximizing `deg(u)+deg(v)`) is a *perfect witness selector on `n ≤ 6`* but
**breaks at `n = 7`** (explicit bipartite counterexamples in the script).
Degree is not a reliable proxy for MIS-frequency — the witness is not locally
readable.

## Where this fits

The graph register is genuinely different (different objects: maximal
independent sets; different proven classes in the literature: chordal-bipartite,
subcubic-bipartite, series-parallel — none of which are the lattice classes).
Yet it re-confirms the campaign's **non-locality** finding from a fourth
independent direction: a clean local witness rule (degree-sum) looks perfect at
small scale and then fails, exactly as the set-side and lattice-side local rules
do.  The cross-register robustness of the non-locality is the substantive
takeaway — not a dead end, but a sharper and sharper description of *what kind of
idea cannot work*.

## Reproduce

```sh
python3 research/frankl_graph_probe.py
```
