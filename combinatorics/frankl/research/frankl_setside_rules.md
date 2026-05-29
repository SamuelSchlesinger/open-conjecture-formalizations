# Set-side novel probe: structural witness-selector rules

Continuation of the open-frontier attack, switching from the lattice side to the
**set side**.  Idea: find a *rule* `R(F)` that picks an element from the *shape*
of a union-closed family `F` (not from frequency directly) such that `R(F)`
always contains an **abundant** element (in ≥ |F|/2 members).  Such a rule, if
valid, is a "Frankl witness selector".

Data-mining over all union-closed families on `[3]` (120) and `[4]` (4958), then
~150k sampled families on `[5]`–`[8]`, surfaced two rules with **zero
failures** anywhere — including adversarial min-size-≥3, min-size-≥4 and
"rare-block" constructions:

- **`minmember`** — *some element of a minimum-size member is abundant.*
  For minimum size `≤ 2` this is exactly the singleton/doubleton cases already
  **proved** in `Frankl.Basic` (`isFranklElement_of_singleton_mem`,
  `isFranklElement_left_or_right_of_pair_mem`).  For minimum size `≥ 3` it is
  open.  Note a single set of size `≥ 3` is *not* an FC-family, so this is a
  genuinely global statement, not forced set-by-set.

- **`invsize`** — *the element maximizing `Σ_{A ∋ x} 1/|A|` is abundant.*
  Equivalently, the most likely element under "pick a uniform member, then a
  uniform element of it".  A specific, computable element — not the trivial
  argmax-frequency.

Both rules are **strictly stronger than Frankl** (they localize the witness), so
they are *falsifiable*: a family where the rule misses every abundant element
would disprove it.  Extensive targeted attempts to falsify them failed.

## The honest meta-finding

Across the whole novel-probing campaign — lattice side (condition (★)) and set
side (`minmember`, `invsize`) — every clean structural rule that *would* help has
the same status:

> It is empirically unbreakable, and **proving it would prove Frankl** (any
> always-valid witness selector implies the conjecture).  So each is
> conjecture-equivalent-or-harder; none is a shortcut.

This is not a dead end so much as a sharp description of *why* Frankl resists:
**no local or simple-structural certificate suffices** — confirmed
independently from two directions.  The rules that look like they should crack
it instead encode the full difficulty.  The rigorous gains of the campaign are
the verified `Frankl.Lattice` lemmas (engine, large-coatom-ideal, modular /
left-modular coatom) and the full Poonen equivalence; the rules here are
honestly-labelled conjecture-equivalent observations, **not** proofs, and add no
`sorry`.

## Reproduce

```sh
python3 research/frankl_setside_rules.py
```
