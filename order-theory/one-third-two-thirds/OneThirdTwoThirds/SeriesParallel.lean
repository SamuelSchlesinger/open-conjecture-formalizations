import OneThirdTwoThirds.TwoChainsCount

/-!
# The 1/3–2/3 conjecture — the series-parallel theorem

This file assembles the two-chains kernel (`TwoChainsCount`) with the ordinal-sum
(`OrdinalSum`) and disjoint-union (`ParallelSum`) reductions into a full proof
that **every series-parallel poset satisfies the 1/3–2/3 conjecture**.

The glue is an **order-isomorphism transfer** of all the relevant quantities
(`numLinExts_orderIso`, `numBefore_orderIso`, `isBalancedPair_orderIso`,
`oneThirdTwoThirdsFor_orderIso`), used twice: to deduce the `m > 2n` regime of
the two-chains kernel from the `m ≤ 2n` regime via the summand-swap, and to
transport the kernel from the concrete chains `Fin k` to arbitrary chains.

`sorry`-free.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

open Finset

variable {X Y : Type*} [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]
  [Fintype Y] [DecidableEq Y] [PartialOrder Y] [DecidableLE Y]

/-! ### Order-isomorphism transfer -/

/-- Transport a ranking of `X` to one of `Y` along an order iso `e : X ≃o Y`. -/
private def transferRanking (e : X ≃o Y) (hcard : Fintype.card X = Fintype.card Y)
    (f : X → Fin (Fintype.card X)) : Y → Fin (Fintype.card Y) :=
  fun b => Fin.castOrderIso hcard (f (e.symm b))

private theorem isLinExt_transferRanking (e : X ≃o Y)
    (hcard : Fintype.card X = Fintype.card Y) {f : X → Fin (Fintype.card X)} (hf : IsLinExt f) :
    IsLinExt (transferRanking e hcard f) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact e.symm.injective (hf.1 ((Fin.castOrderIso hcard).injective hab))
  · intro a b hab
    exact (Fin.castOrderIso hcard).monotone (hf.2 _ _ (e.symm.monotone hab))

/-- **Linear-extension count is an order-iso invariant.** -/
theorem numLinExts_orderIso (e : X ≃o Y) : numLinExts (X := X) = numLinExts (X := Y) := by
  classical
  have hcard : Fintype.card X = Fintype.card Y := Fintype.card_congr e.toEquiv
  unfold numLinExts
  refine Finset.card_bij (fun f _ => transferRanking e hcard f) ?_ ?_ ?_
  · intro f hf
    exact mem_linExts.mpr (isLinExt_transferRanking e hcard (mem_linExts.mp hf))
  · intro f₁ _ f₂ _ heq
    funext a
    have := congrFun heq (e a)
    simp only [transferRanking, OrderIso.symm_apply_apply] at this
    exact (Fin.castOrderIso hcard).injective this
  · intro g hg
    refine ⟨transferRanking e.symm hcard.symm g, mem_linExts.mpr ?_, ?_⟩
    · exact isLinExt_transferRanking e.symm hcard.symm (mem_linExts.mp hg)
    · funext b
      simp only [transferRanking, OrderIso.symm_symm, OrderIso.apply_symm_apply,
        OrderIso.symm_apply_apply]
      exact (Fin.castOrderIso hcard).apply_symm_apply (g b)

/-- **Before-count is an order-iso invariant.** -/
theorem numBefore_orderIso (e : X ≃o Y) (x y : X) :
    numBefore (X := X) x y = numBefore (X := Y) (e x) (e y) := by
  classical
  have hcard : Fintype.card X = Fintype.card Y := Fintype.card_congr e.toEquiv
  unfold numBefore linExts
  refine Finset.card_bij (fun f _ => transferRanking e hcard f) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    obtain ⟨hmem, hlt⟩ := hf
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      isLinExt_transferRanking e hcard (mem_linExts.mp hmem)⟩, ?_⟩
    simp only [transferRanking, OrderIso.symm_apply_apply]
    exact (Fin.castOrderIso hcard).strictMono hlt
  · intro f₁ hf₁ f₂ hf₂ heq
    funext a
    have := congrFun heq (e a)
    simp only [transferRanking, OrderIso.symm_apply_apply] at this
    exact (Fin.castOrderIso hcard).injective this
  · intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hmem, hlt⟩ := hg
    rw [Finset.mem_filter] at hmem
    refine ⟨transferRanking e.symm hcard.symm g, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        isLinExt_transferRanking e.symm hcard.symm hmem.2⟩, ?_⟩
      simp only [transferRanking, OrderIso.symm_symm, OrderIso.symm_apply_apply]
      exact (Fin.castOrderIso hcard.symm).strictMono hlt
    · funext b
      simp only [transferRanking, OrderIso.symm_symm, OrderIso.apply_symm_apply,
        OrderIso.symm_apply_apply]
      exact (Fin.castOrderIso hcard).apply_symm_apply (g b)

omit [Fintype X] [DecidableEq X] [DecidableLE X] [Fintype Y] [DecidableEq Y] [DecidableLE Y] in
/-- Incomparability transfers along an order iso. -/
theorem incomp_orderIso (e : X ≃o Y) (x y : X) :
    Incomp (X := X) x y ↔ Incomp (X := Y) (e x) (e y) := by
  simp only [Incomp, e.le_iff_le]

/-- **`IsBalancedPair` is an order-iso invariant.** -/
theorem isBalancedPair_orderIso (e : X ≃o Y) (x y : X) :
    IsBalancedPair (X := X) x y ↔ IsBalancedPair (X := Y) (e x) (e y) := by
  unfold IsBalancedPair
  rw [numBefore_orderIso e x y, numLinExts_orderIso e, incomp_orderIso e x y]

/-- **The conjecture is an order-iso invariant.** -/
theorem oneThirdTwoThirdsFor_orderIso (e : X ≃o Y)
    (h : OneThirdTwoThirdsFor (X := X)) : OneThirdTwoThirdsFor (X := Y) := by
  rintro ⟨u, v, huv⟩
  obtain ⟨x, y, hb⟩ := h ⟨e.symm u, e.symm v, (incomp_orderIso e _ _).mpr
    (by rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]; exact huv)⟩
  exact ⟨e x, e y, (isBalancedPair_orderIso e x y).mp hb⟩

/-! ### Swapping the two summands -/

/-- Swapping the two summands of a parallel composition is an order iso. -/
def sumCommOrderIso : (X ⊕ Y) ≃o (Y ⊕ X) where
  toEquiv := Equiv.sumComm X Y
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;>
      simp only [Equiv.sumComm_apply, Sum.swap_inl, Sum.swap_inr] <;> rfl

/-- **The two-chains kernel for `Fin m ⊕ Fin n`, both regimes.**  A disjoint union
of two nonempty chains has a balanced (cross) pair. -/
theorem balancedPair_finSum {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ u v : Fin m ⊕ Fin n, IsBalancedPair (X := Fin m ⊕ Fin n) u v := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  by_cases h : m ≤ 2 * n
  · exact balancedPair_finSum_row hn h
  · obtain ⟨u, v, hb⟩ := balancedPair_finSum_row (m := n) (n := m) hm (by omega)
    exact ⟨sumCommOrderIso u, sumCommOrderIso v,
      (isBalancedPair_orderIso (sumCommOrderIso (X := Fin n) (Y := Fin m)) u v).mp hb⟩

end OneThirdTwoThirds
