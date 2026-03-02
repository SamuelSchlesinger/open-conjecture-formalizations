import Fortune.Defs
import Fortune.Literature
import Mathlib.NumberTheory.Primorial

namespace Fortune

/-!
# TODO Roadmap (Fortune)

This file is a planning checkpoint for the next research-focused formalization pass.
It records concrete target statements and implementation notes for the six expansion
routes identified after the initial literature formalization.

Conventions:
- `TODO_*` declarations below are **target propositions** (not yet proved).
- Each target includes enough context to begin implementation later.
- Keep this file synchronized with `README.md` and `references.md`.
-/

/-- TODO Route 1.A (bridge): identify the indexed primorial used in `Defs`
with the threshold primorial used in literature theorems. -/
def TODO_bridge_nthPrimorial_eq_primorial_lastIncludedPrime : Prop :=
  ∀ n : Nat, 1 ≤ n → nthPrimorial n = primorial (lastIncludedPrime n)

/-- TODO Route 1.B (bridge): transfer least-offset statements between
the `n`-indexed model and the prime-threshold model. -/
def TODO_bridge_leastOffset_indexed_to_threshold : Prop :=
  ∀ n m : Nat, 1 ≤ n →
    (IsLeastFortunateOffset n m ↔ IsLeastFortunateOffsetAtPrime (lastIncludedPrime n) m)

/-- TODO Route 1.C (bridge): derive a consecutive-prime witness for each `n`
at the threshold `lastIncludedPrime n`. -/
def TODO_bridge_exists_nextPrime_at_lastIncluded : Prop :=
  ∀ n : Nat, 1 ≤ n →
    ∃ r : Nat, ConsecutivePrimes (lastIncludedPrime n) r

/-- TODO Route 2.A (reduction): quantitative bound that would imply Fortune once
Routes 1.A/1.B/1.C are in place. -/
def TODO_reduction_bound_m_lt_nextPrime_sq : Prop :=
  ∀ n m r : Nat, 1 ≤ n →
    IsLeastFortunateOffset n m →
    ConsecutivePrimes (lastIncludedPrime n) r →
    m < r ^ 2

/-- TODO Route 2.B (reduction theorem): explicit implication from the quantitative
bound to `FortuneConjecture`. -/
def TODO_reduction_bound_implies_fortune : Prop :=
  TODO_reduction_bound_m_lt_nextPrime_sq → FortuneConjecture

/-- TODO Route 3 (Kaczorowski–Szydło, 2007):
formalize explicit congruence obstruction theorems from the paper.

Implementation checklist:
1. Add exact theorem statements from Kaczorowski–Szydło to Lean as definitions
   in a new module `Fortune/Congruence.lean`.
2. Prove each statement from its arithmetic hypotheses, avoiding `simp`-only
   black boxes on modular arithmetic.
3. Connect each obstruction theorem to `IsFortunateOffset` or
   `IsLeastFortunateOffset` as corollaries.
4. Add source citations in theorem docstrings with theorem numbers/page refs.
-/
def TODO_formalize_kaczorowski_szydlo_congruence_obstructions : Prop :=
  True

/-- TODO Route 4 (not yet started): strengthen composite-offset structure from
`minFac` bounds to richer prime-divisor profile constraints. -/
def TODO_strengthen_composite_offset_prime_divisor_profile : Prop :=
  True

/-- TODO Route 5 (not yet started): tighten the formal Theorem 18 variant in
`Fortune.Literature` by deriving/removing auxiliary side-conditions when possible. -/
def TODO_tighten_lower_interval_theorem18_variant : Prop :=
  True

/-- TODO Route 6 (not yet started): extend certified finite computation range
for least offsets with reproducible proof-producing checks. -/
def TODO_extend_certified_computation_range : Prop :=
  True

end Fortune
