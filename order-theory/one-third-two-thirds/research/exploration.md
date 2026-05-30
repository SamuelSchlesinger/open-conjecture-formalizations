# 1/3–2/3 conjecture — computational exploration (Phase 3)

Scripts: `explore.py` (exhaustive `n ≤ 5`, reductions, selection rules) and
`explore_large.py` (random stress `n = 6..9`, extremal-structure analysis).
All counts are exact integers; ratios are `fractions.Fraction`.  `e(P)` and the
before-counts are computed by the standard order-ideal DP
(`f(S) = Σ_{m maximal in S} f(S∖{m})`, `e(P)=f(full)`; `e(P,x<y)` by re-running
the DP on `P` with the extra relation `x<y` added).

## 1. The conjecture holds where we can check it

| n | labelled posets | non-chains | min δ(P) | violations |
|---|---|---|---|---|
| 2 | 3 | 1 | 1/2 | 0 |
| 3 | 19 | 13 | **1/3** | 0 |
| 4 | 219 | 195 | **1/3** | 0 |
| 5 | 4231 | 4111 | **1/3** | 0 |

Random stress test (≈3000 sampled non-chain posets each, mixed densities):

| n | sampled | min δ found | violations |
|---|---|---|---|
| 6 | 2896 | 1/3 | 0 |
| 7 | 2934 | 1/3 | 0 |
| 8 | 2962 | 1/3 | 0 |
| 9 | 2983 | 1/3 | 0 |

`δ(P) ≥ 1/3` held in **every** poset examined. The minimum `1/3` is attained
(not approached), confirming Linial's tightness exactly.

## 2. Structure of the extremal (δ = 1/3) posets — a clean observation

Among **all** labelled posets with `n ≤ 5`, *every* poset achieving `δ(P) = 1/3`
has **exactly `e(P) = 3` linear extensions** (6 of them at `n=3`, 48 at `n=4`,
360 at `n=5`). In each, the best incomparable pair splits the 3 extensions
`1 : 2`, giving `min(δ, 1−δ) = 1/3` exactly.

So in this range the tight constant `1/3` is realized *only* by the rigid
"three-extension" posets — those order-isomorphic, up to adding comparabilities,
to the single-relation poset `V3` (`a<b`, `c` free). This matches the Lean
tightness witness `SmallCases.V3`. (Note: this is the global *minimum* of `δ`.
Sah's width-2 families have `δ → ≈0.3488 > 1/3`, so they are extremal for the
width-2 sub-problem, not for the global minimum.)

## 3. Reductions tested (the "Frankl playbook")

### Duality — **clean, holds exactly** ✓ (now formalized in Lean)
`δ(P) = δ(P^op)` in all 4320 non-chain posets with `n ≤ 5`. Reason: reversing a
linear extension is a bijection `ext(P) ↔ ext(P^op)` sending "`x` before `y`" to
"`y` before `x`", so `e(P^op, x<y) = e(P, y<x)`; the pairwise balance
`min(δ(x,y), δ(y,x))` is invariant. This is proved sorry-free in
`OneThirdTwoThirds.Duality` (`numBefore_orderDual`, `isBalancedPair_orderDual`,
`oneThirdTwoThirdsFor_orderDual`).

### Element deletion — **does NOT lift** ✗ (honest negative)
"A balanced pair of `P∖{z}` is a balanced pair of `P`" **fails**: 2640 `(z,pair)`
instances over `n ≤ 5` where the sub-poset's balanced pair is either comparable
in `P` or unbalanced in `P`. Smallest witness: the "N" poset
`< = {(1,2),(1,3),(3,2)}` on 4 elements — deleting any element leaves a pair
that is unbalanced once the deleted relations are restored. So deletion is not a
valid reduction for balanced pairs (unlike Frankl's twin-deletion). The count
`e(P)` is genuinely non-local in the element set.

### Ordinal sums / antichain stacks
Ordinal sums of antichains and "broom" posets (chain + one free element) sit at
`δ = 1/2` except the single-relation `n=3` broom (`δ = 1/3`). Stacking blocks
raises `δ` toward `1/2`; the rigidity that forces `δ = 1/3` is destroyed by
extra free elements.

## 4. Selection rules — the balanced pair is non-local

Can a *simple, local* rule always pick a balanced incomparable pair? Over all
`n ≤ 5` non-chains:

| rule | failures |
|---|---|
| A: pick pair minimizing `\|2·e(P,x<y) − e(P)\|` (closest to ½) | **0 / 4320** |
| B: first incomparable pair (lexicographic) | 1342 / 4320 (31%) |
| C: both elements minimal | 1036 / 3290 (31%) |

Rule A never fails — but that is *exactly the conjecture restated*: the most
balanced pair is balanced. The naive local rules B and C fail a third of the
time. **There is no local/greedy selection rule** (in the rules tried): choosing
the balanced pair requires comparing actual extension counts, which are global.
This is the same "non-locality" texture seen in the Frankl campaign — the
witness cannot be read off the Hasse diagram locally.

## 5. Takeaways for the Lean attack

- **Formalize duality** (done): a genuine, sorry-free reduction halving the
  search and a template for further symmetry reductions.
- **Do not** attempt a deletion/quotient reduction for balanced pairs — the data
  refutes the naive lift (cf. the analogous failed Frankl congruence-quotient
  reduction).
- The extremal `e(P)=3` characterization suggests the right *tightness* invariant
  is rigidity (small `e(P)`), not width or height alone.
- A constant-pushing Lean target (toward Kahn–Saks `3/11` or BFT `(5−√5)/10`)
  would need the FKG / Ahlswede–Daykin machinery already in Mathlib
  (`Finset.four_functions_theorem`, `fkg`) — the realistic next lift.
