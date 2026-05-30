import OneThirdTwoThirds.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# The 1/3–2/3 conjecture — small cases

This file is the computational sanity check on the counting infrastructure of
`Defs`/`Basic`, and it formalizes the **tightness** of the constant `1/3`.

## Chains

A totally ordered poset has no incomparable pair, so it satisfies the
conjecture vacuously (`oneThirdTwoThirdsFor_of_total` from `Basic`).  We record
this for the canonical chain `Fin n`.

## The tight three-element poset (Linial 1984)

`V3` is the poset on `{a, b, c}` whose only strict relation is `a < b`
(`c` is incomparable to both).  Its three linear extensions are `abc`, `acb`,
`cab`, so `e(P) = 3`.  For the incomparable pair `{a, c}` we have
`e(P, a<c) = 2` and `e(P, c<a) = 1`, giving `δ(a,c) = 2/3` and the *minimum*
balance `min(δ(a,c), δ(c,a)) = 1/3` — exactly the lower endpoint.  The same
holds for `{b, c}`.  Hence:

* `V3` is a non-chain with a balanced pair (`oneThirdTwoThirdsFor_V3`), so the
  conjecture holds for it; and
* **every** incomparable pair of `V3` has `min`-balance exactly `1/3`
  (`V3_balance_tight`), so the constant `1/3` in the conjecture cannot be
  replaced by anything larger.  This is Linial's tightness example.

All counts are verified by the kernel (`decide`), so they are axiom-clean
(no `native_decide`).
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

/-! ### Chains satisfy the conjecture -/

/-- Every finite chain (here the canonical example `Fin n`) satisfies the
conjecture vacuously: it has no incomparable pair. -/
theorem oneThirdTwoThirdsFor_fin (n : ℕ) : OneThirdTwoThirdsFor (X := Fin n) :=
  oneThirdTwoThirdsFor_of_total (fun a b => le_total a b)

/-! ### The tight three-element poset -/

namespace V3

/-- The three-element type `{a, b, c}` carrying the single-relation poset. -/
inductive Elt | a | b | c
deriving DecidableEq, Fintype

open Elt

/-- The order: reflexive, plus the single strict relation `a < b`. -/
instance : LE Elt := ⟨fun x y => x = y ∨ (x = a ∧ y = b)⟩

instance : DecidableLE Elt := fun x y => by unfold LE.le instLEElt; infer_instance

instance : PartialOrder Elt where
  le := (· ≤ ·)
  le_refl _ := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with h | ⟨hx, hy⟩
    · subst h; exact hyz
    · rcases hyz with h | ⟨hy', _⟩
      · subst h; exact Or.inr ⟨hx, hy⟩
      · subst hy; cases hy'
  le_antisymm x y hxy hyx := by
    rcases hxy with h | ⟨hx, hy⟩
    · exact h
    · rcases hyx with h | ⟨hy', _⟩
      · exact h.symm
      · subst hx; subst hy; cases hy'

end V3

open V3 Elt

/-- `e(V3) = 3`: the linear extensions are `abc`, `acb`, `cab`. -/
theorem V3_numLinExts : numLinExts (X := Elt) = 3 := by decide

/-- `e(V3, a<c) = 2`. -/
theorem V3_before_ac : numBefore (a) (c) = 2 := by decide

/-- `e(V3, c<a) = 1`. -/
theorem V3_before_ca : numBefore (c) (a) = 1 := by decide

/-- `e(V3, b<c) = 1`. -/
theorem V3_before_bc : numBefore (b) (c) = 1 := by decide

/-- `e(V3, c<b) = 2`. -/
theorem V3_before_cb : numBefore (c) (b) = 2 := by decide

/-- The pair `{a, c}` is balanced: `δ(a,c) = 2/3`, which lies in `[1/3, 2/3]`.
(Here `3·e(P,a<c) = 6 = 2·e(P)`, so it sits exactly at the upper endpoint;
equivalently `{c, a}` sits at the lower endpoint `1/3`.) -/
theorem V3_balanced_ac : IsBalancedPair (a) (c) := by decide

/-- `V3` is not a chain: `a` and `c` are incomparable. -/
theorem V3_isNotChain : IsNotChain (X := Elt) := ⟨a, c, by decide⟩

/-- The 1/3–2/3 conjecture holds for `V3` (witnessed by the pair `{a, c}`). -/
theorem oneThirdTwoThirdsFor_V3 : OneThirdTwoThirdsFor (X := Elt) :=
  fun _ => ⟨a, c, V3_balanced_ac⟩

/-- **Tightness of `1/3` (Linial 1984).**  In `V3`, every incomparable pair
`{x, y}` has minimum balance exactly `1/3`: `3 · min(e(P,x<y), e(P,y<x)) = e(P)`.
Since no incomparable pair does better than `1/3`, the constant in the
conjecture cannot be improved. -/
theorem V3_balance_tight :
    ∀ x y : Elt, Incomp x y →
      3 * min (numBefore x y) (numBefore y x) = numLinExts (X := Elt) := by
  decide

end OneThirdTwoThirds
