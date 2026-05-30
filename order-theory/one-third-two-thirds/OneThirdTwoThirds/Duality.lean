import OneThirdTwoThirds.Basic
import Mathlib.Order.Fin.Basic

/-!
# The 1/3–2/3 conjecture — order duality

The computational exploration (`research/exploration.md`) found that
`δ(P) = δ(P^op)` in **every** poset tested (4320 non-chains with `n ≤ 5`, zero
mismatches).  This file turns that observation into an *analytic*, general
theorem: order duality is an exact symmetry of the balance problem.

The mechanism is the **order-reversal bijection** on linear extensions.
Reversing a ranking, `f ↦ Fin.rev ∘ f` (send each position `p` to `n-1-p`),
sends a linear extension of `P` to a linear extension of the dual poset `Pᵒᵈ`
and exchanges "`x` before `y`" with "`y` before `x`".  Hence

  `e(Pᵒᵈ) = e(P)`            (`numLinExts_orderDual`)
  `e(Pᵒᵈ, x<y) = e(P, y<x)`  (`numBefore_orderDual`)

from which the balanced-pair predicate and the whole conjecture transfer between
`P` and `Pᵒᵈ` (`isBalancedPair_orderDual`, `oneThirdTwoThirdsFor_orderDual`).

Consequences:
* the conjecture for `P` is **equivalent** to the conjecture for `Pᵒᵈ`, so one may
  always assume a convenient orientation (e.g. work with a minimal rather than a
  maximal element); and
* `δ(P) = δ(Pᵒᵈ)` exactly, confirming the experiment.

Everything here is `sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {X : Type*} [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]

/-- Reversal of a ranking: compose with `Fin.rev`.  As a function it lands in
`Xᵒᵈ → Fin |Xᵒᵈ|` (the carriers and cardinalities of `X` and `Xᵒᵈ` agree
definitionally).  Reversing positions turns a linear extension of `P` into one
of the dual poset `Pᵒᵈ`. -/
def revRanking (f : X → Fin (Fintype.card X)) : Xᵒᵈ → Fin (Fintype.card Xᵒᵈ) :=
  fun a => (f (OrderDual.ofDual a)).rev

omit [DecidableEq X] [PartialOrder X] [DecidableLE X] in
@[simp] theorem revRanking_apply (f : X → Fin (Fintype.card X)) (a : Xᵒᵈ) :
    revRanking f a = (f (OrderDual.ofDual a)).rev := rfl

omit [DecidableEq X] [PartialOrder X] [DecidableLE X] in
/-- Reversing twice is the identity (`Fin.rev` is an involution). -/
theorem revRanking_revRanking (f : X → Fin (Fintype.card X)) :
    revRanking (revRanking f) = f := by
  funext a; exact Fin.rev_rev _

omit [DecidableEq X] [DecidableLE X] in
/-- `revRanking` sends linear extensions of `P` to linear extensions of `Pᵒᵈ`. -/
theorem isLinExt_revRanking {f : X → Fin (Fintype.card X)} (hf : IsLinExt f) :
    IsLinExt (X := Xᵒᵈ) (revRanking f) := by
  obtain ⟨hinj, hmono⟩ := hf
  refine ⟨?_, ?_⟩
  · intro a b hab
    simp only [revRanking_apply] at hab
    exact congrArg OrderDual.toDual (hinj (Fin.rev_injective hab))
  · intro a b hab
    -- `a ≤ b` in `Xᵒᵈ` means `ofDual b ≤ ofDual a` in `X`
    have hba : OrderDual.ofDual b ≤ OrderDual.ofDual a := hab
    simp only [revRanking_apply]
    rw [Fin.rev_le_rev]
    exact hmono _ _ hba

/-- **Linear extensions are preserved by duality**: `e(P) = e(Pᵒᵈ)`. -/
theorem numLinExts_orderDual : numLinExts (X := X) = numLinExts (X := Xᵒᵈ) := by
  unfold numLinExts linExts
  refine Finset.card_bij (fun f _ => revRanking f) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨Finset.mem_univ _, isLinExt_revRanking hf.2⟩
  · intro f₁ _ f₂ _ heq
    -- revRanking injective: evaluate at toDual c
    funext c
    have := congrFun heq (OrderDual.toDual c)
    simp only [revRanking_apply, OrderDual.ofDual_toDual] at this
    exact Fin.rev_injective this
  · intro g hg
    rw [Finset.mem_filter] at hg
    refine ⟨revRanking g, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, isLinExt_revRanking hg.2⟩
    · exact revRanking_revRanking g

/-- **The before-count flips under duality**: `e(P, y<x) = e(Pᵒᵈ, x<y)`.
A linear extension of `P` puts `y` before `x` exactly when its reversal (a
linear extension of `Pᵒᵈ`) puts `x` before `y`. -/
theorem numBefore_orderDual (x y : X) :
    numBefore (X := X) y x
      = numBefore (X := Xᵒᵈ) (OrderDual.toDual x) (OrderDual.toDual y) := by
  unfold numBefore linExts
  refine Finset.card_bij (fun f _ => revRanking f) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    obtain ⟨hmem, hlt⟩ := hf
    rw [Finset.mem_filter] at hmem
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, isLinExt_revRanking hmem.2⟩, ?_⟩
    -- goal: revRanking f (toDual x) < revRanking f (toDual y); have hlt : f y < f x
    simp only [revRanking_apply, OrderDual.ofDual_toDual]
    exact Fin.rev_lt_rev.mpr hlt
  · intro f₁ _ f₂ _ heq
    funext c
    have := congrFun heq (OrderDual.toDual c)
    simp only [revRanking_apply, OrderDual.ofDual_toDual] at this
    exact Fin.rev_injective this
  · intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hmem, hlt⟩ := hg
    rw [Finset.mem_filter] at hmem
    refine ⟨revRanking g, ?_, revRanking_revRanking g⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, isLinExt_revRanking hmem.2⟩, ?_⟩
    -- goal: revRanking g y < revRanking g x; have hlt : g (toDual x) < g (toDual y)
    simp only [revRanking_apply]
    exact Fin.rev_lt_rev.mpr hlt

omit [Fintype X] [DecidableEq X] [DecidableLE X] in
/-- Incomparability is a self-dual notion. -/
theorem incomp_orderDual (x y : X) :
    Incomp (X := Xᵒᵈ) (OrderDual.toDual x) (OrderDual.toDual y) ↔ Incomp (X := X) x y :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Balanced pairs are preserved by duality.**  `{x, y}` is balanced in `Pᵒᵈ`
iff it is balanced in `P`. -/
theorem isBalancedPair_orderDual (x y : X) :
    IsBalancedPair (X := Xᵒᵈ) (OrderDual.toDual x) (OrderDual.toDual y)
      ↔ IsBalancedPair (X := X) x y := by
  unfold IsBalancedPair
  rw [← numBefore_orderDual, ← numLinExts_orderDual, incomp_orderDual]
  -- LHS now: Incomp x y ∧ e ≤ 3·before(y,x) ∧ 3·before(y,x) ≤ 2·e
  -- which is exactly `IsBalancedPair y x`; transport by symmetry.
  constructor
  · intro h
    exact (isBalancedPair_comm (X := X)).mp ⟨h.1.symm, h.2⟩
  · intro h
    have h' := (isBalancedPair_comm (X := X)).mpr h
    exact ⟨h'.1.symm, h'.2⟩

/-- **The conjecture is self-dual.**  It holds for `P` iff it holds for `Pᵒᵈ`. -/
theorem oneThirdTwoThirdsFor_orderDual :
    OneThirdTwoThirdsFor (X := Xᵒᵈ) ↔ OneThirdTwoThirdsFor (X := X) := by
  constructor
  · intro h hnc
    obtain ⟨x, y, hxy⟩ := hnc
    obtain ⟨a, b, hab⟩ := h ⟨OrderDual.toDual x, OrderDual.toDual y,
      (incomp_orderDual x y).mpr hxy⟩
    exact ⟨OrderDual.ofDual a, OrderDual.ofDual b,
      (isBalancedPair_orderDual (OrderDual.ofDual a) (OrderDual.ofDual b)).mp hab⟩
  · intro h hnc
    obtain ⟨x, y, hxy⟩ := hnc
    obtain ⟨a, b, hab⟩ := h ⟨OrderDual.ofDual x, OrderDual.ofDual y,
      (incomp_orderDual _ _).mp hxy⟩
    exact ⟨OrderDual.toDual a, OrderDual.toDual b,
      (isBalancedPair_orderDual a b).mpr hab⟩

end OneThirdTwoThirds
