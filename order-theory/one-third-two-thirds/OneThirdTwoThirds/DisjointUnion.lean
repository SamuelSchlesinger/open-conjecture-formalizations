import OneThirdTwoThirds.Symmetry
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Sum

/-!
# The 1/3–2/3 conjecture — disjoint unions and a non-twin balanced pair

The **parallel composition** (disjoint union) `P ⊕ Q` of two posets keeps the two
summands incomparable.  For the self-union `P ⊕ P`, swapping the two copies
(`Equiv.sumComm`) is an order-automorphism exchanging `inl x` and `inr x`; these
are incomparable, so by `Symmetry.isBalancedPair_of_orderIso_swap` the pair
`{inl x, inr x}` is balanced (`δ = 1/2`).  Hence **`P ⊕ P` satisfies the 1/3–2/3
conjecture** for every nonempty `P` (`oneThirdTwoThirdsFor_sum_self`).

Note this balanced pair is generally **not** a twin pair: `inl x` and `inr x`
have different relations to a third element `inl z` (one is `x ≤ z`, the other is
incomparable).  So this genuinely exercises the *global*-automorphism lemma
beyond the local twin condition.  `sorry`-free.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {α β : Type*}

/-- Parallel composition order on a disjoint union: `inl`s are ordered by `α`,
`inr`s by `β`, and an `inl` is never comparable to an `inr`. -/
instance instPartialOrderSum [PartialOrder α] [PartialOrder β] : PartialOrder (α ⊕ β) where
  le x y := match x, y with
    | Sum.inl a, Sum.inl b => a ≤ b
    | Sum.inr a, Sum.inr b => a ≤ b
    | _, _ => False
  le_refl x := by cases x with | inl a => exact le_refl a | inr a => exact le_refl a
  le_trans x y z := by
    cases x <;> cases y <;> cases z <;> intro hxy hyz <;>
      first
        | exact le_trans hxy hyz
        | exact hxy.elim
        | exact hyz.elim
  le_antisymm x y := by
    cases x <;> cases y <;> intro hxy hyx <;>
      first
        | exact congrArg Sum.inl (le_antisymm hxy hyx)
        | exact congrArg Sum.inr (le_antisymm hxy hyx)
        | exact hxy.elim

instance instDecidableLESum [PartialOrder α] [PartialOrder β] [DecidableLE α] [DecidableLE β] :
    DecidableLE (α ⊕ β) := fun x y =>
  match x, y with
  | Sum.inl a, Sum.inl b => inferInstanceAs (Decidable (a ≤ b))
  | Sum.inr a, Sum.inr b => inferInstanceAs (Decidable (a ≤ b))
  | Sum.inl _, Sum.inr _ => isFalse not_false
  | Sum.inr _, Sum.inl _ => isFalse not_false

/-- An `inl` and an `inr` are always incomparable in the parallel composition. -/
theorem incomp_inl_inr [PartialOrder α] [PartialOrder β] (a : α) (b : β) :
    Incomp (Sum.inl a) (Sum.inr b) :=
  ⟨fun h => h.elim, fun h => h.elim⟩

/-- Swapping the two copies of `α ⊕ α` is an order-automorphism. -/
def sumSwapOrderIso [PartialOrder α] : (α ⊕ α) ≃o (α ⊕ α) where
  toEquiv := Equiv.sumComm α α
  map_rel_iff' := by intro x y; cases x <;> cases y <;> rfl

@[simp] theorem sumSwapOrderIso_inl [PartialOrder α] (a : α) :
    sumSwapOrderIso (Sum.inl a) = Sum.inr a := rfl

@[simp] theorem sumSwapOrderIso_inr [PartialOrder α] (a : α) :
    sumSwapOrderIso (Sum.inr a) = Sum.inl a := rfl

/-- For every `x`, the incomparable pair `{inl x, inr x}` of `P ⊕ P` is balanced
(`δ = 1/2`): the copy-swap automorphism exchanges them. -/
theorem isBalancedPair_inl_inr [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableLE α]
    (x : α) : IsBalancedPair (X := α ⊕ α) (Sum.inl x) (Sum.inr x) :=
  isBalancedPair_of_orderIso_swap sumSwapOrderIso (sumSwapOrderIso_inl x)
    (sumSwapOrderIso_inr x) (incomp_inl_inr x x)

/-- **`P ⊕ P` satisfies the 1/3–2/3 conjecture.**  A self disjoint union is never
a chain (if nonempty) and has the balanced pair `{inl x, inr x}`. -/
theorem oneThirdTwoThirdsFor_sum_self
    [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableLE α] :
    OneThirdTwoThirdsFor (X := α ⊕ α) := by
  rintro ⟨u, _, _⟩
  obtain a | a := u <;>
    exact ⟨Sum.inl a, Sum.inr a, isBalancedPair_inl_inr a⟩

end OneThirdTwoThirds
