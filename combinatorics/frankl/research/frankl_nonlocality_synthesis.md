# Why Frankl is non-local: a synthesis across the attack angles

A synthesis of the open-frontier campaign (2026-05-28).  Every angle we tried —
set-side injections, the lattice form, condition (★), the witness-selector rules
`minmember`/`invsize`, the entropy method, FKG — turns out to be the *same*
obstruction in different language.  This note records the unifying picture.
(The framing is an interpretive lens, not a theorem; the cited facts are real.)

## The shared skeleton: "add x, then come back"

To certify that an element `x` is abundant, every method builds an injection (or
a fractional / entropy analogue) from *the world without x* into *the world with
x*:

| method | the "add x" map | breaks because |
|--------|-----------------|----------------|
| singleton `{x}` | `B ↦ B∪{x}` (perfect matching) | — (works) |
| doubleton `{a,b}` | union on a 2-D block | — (works) |
| lattice up-set `↑x` | `α ↦ m⊓α` | needs the **modular law** to invert |
| entropy (Gilmer) | soft injection via `H(A∪B)` | discards correlation; caps at `(3−√5)/2` |

Going **up** (adding `x`, taking unions) is free — that is exactly what
union-closure provides.  The difficulty is always **coming back down**:
recovering the preimage, inverting `∪`.  Union-closure provides *no descent
structure*.  It is a one-directional algebra.

## Non-locality = the missing descent

Each method dies precisely where descent fails:

- **size-≥3 set**: `B ↦ B∪A` is injective only on `B` disjoint from `A`;
  partially-overlapping `B` are unrecoverable.
- **non-modular lattice**: `α ↦ m⊓α` fails to be injective because `α` is no
  longer recovered as `x ⊔ (m⊓α)` — but that recovery identity *is* the modular
  law.  Its failure (`N₅`) is the obstruction.  Empirically every lattice in the
  `B₄` census that escaped all elementary certificates is non-modular.
- **entropy**: the loss in `H(A∪B)` vs `H(A)+H(B)` is the mutual information
  discarded by the independence (iid) assumption.
- **FKG**: `1_F` is not log-supermodular (`A,B∈F` says nothing about `A∩B`), so
  the one inequality that would give descent does not apply.

## Confirmations

- **Literature frontier = meet-control.** Provable classes form a ladder of
  meet–join compatibility: distributive → modular → lower-semimodular
  (Reinhold) → … → general (open).  The proven/open boundary sits at
  *semimodularity*, the edge of meet-control — the same place our elementary
  injections die.
- **Why `1/2`.** A descent-free ascent is a one-sided count; ascent + independence
  caps at the entropy ceiling `(3−√5)/2 ≈ 0.382`, and the leftover `≈ 0.118` to
  `1/2` is exactly the descent/correlation thrown away.  `1/2` is the balance
  point of the Boolean cube `2^[n]` — everywhere-tight, fully symmetric — so any
  method must be tight there with no asymmetry to exploit.
- **Self-balancing** (the (★) phenomenon) and **conjecture-equivalence** of clean
  rules both follow: ascent is free *and forced* (a small-set element floods
  upward into every union), so local quantities are conserved/coupled and cannot
  be decoupled; and a clean witness-selector would be a uniform descent recipe,
  which is exactly what is absent — so any working rule already contains the full
  argument (hence conjecture-hard).

## Compass for a winning idea

Local witness-selectors are provably conjecture-equivalent — stop hunting them.
The escape must **supply the missing descent globally, not pointwise**: a global
invariant of the join-semilattice that encodes descent without requiring it
locally, or a genuinely *correlated* (non-iid) entropy/transport bound (the
direction AHS/Sawin nudge, `0.382 → 0.382+ε`, and why progress is slow).

## Provenance

- *Facts:* modular law = recovery identity; B₄ escapers are non-modular; `1_F`
  not log-supermodular; literature frontier at semimodularity; entropy ceiling
  `(3−√5)/2`; `2^[n]` everywhere-tight.
- *Lens:* the ascent-free / missing-descent framing — interpretive, but it
  retro-predicts every observed break point and the literature boundary.
- Supporting experiments: `lattice_frankl_attack.py`,
  `lattice_frankl_adversarial.py`, `frankl_setside_rules.py`.
