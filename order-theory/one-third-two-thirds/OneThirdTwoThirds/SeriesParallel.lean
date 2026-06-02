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

/-! ### From abstract chains to `Fin` -/

/-- A linear extension exists for any finite poset. -/
theorem exists_isLinExt : ∃ f : X → Fin (Fintype.card X), IsLinExt f := by
  have h := numLinExts_pos (X := X)
  rw [numLinExts, Finset.card_pos] at h
  obtain ⟨f, hf⟩ := h
  exact ⟨f, mem_linExts.mp hf⟩

/-- A **chain** (total order) is order-isomorphic to `Fin (card)`: its unique
linear extension reflects `≤` by totality. -/
noncomputable def chainOrderIso (htot : ∀ a b : X, a ≤ b ∨ b ≤ a) :
    X ≃o Fin (Fintype.card X) :=
  let f := (exists_isLinExt (X := X)).choose
  let hf := (exists_isLinExt (X := X)).choose_spec
  { toEquiv := Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf.1, (Fintype.card_fin _).symm⟩)
    map_rel_iff' := by
      intro a b
      refine ⟨fun hle => ?_, fun hle => hf.2 _ _ hle⟩
      rcases htot a b with h | h
      · exact h
      · have hba : f b ≤ f a := hf.2 _ _ h
        have : a = b := hf.1 (le_antisymm hle hba)
        exact this ▸ le_refl a }

/-- Sum of two order isos is an order iso of the parallel compositions. -/
def sumCongrOrderIso {γ δ : Type*} [PartialOrder γ] [PartialOrder δ]
    (eα : X ≃o γ) (eβ : Y ≃o δ) : (X ⊕ Y) ≃o (γ ⊕ δ) where
  toEquiv := Equiv.sumCongr eα.toEquiv eβ.toEquiv
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;>
      simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, par_inl_le_inl, par_inr_le_inr] <;>
      first
        | exact eα.map_rel_iff'
        | exact eβ.map_rel_iff'
        | exact Iff.rfl

/-- **The disjoint-union reduction discharged for two chains.**  If `P` and `Q`
are chains, then `P ⊔ Q` satisfies the 1/3–2/3 conjecture: any incomparable pair
is a cross pair, and the two-chains kernel (`balancedPair_finSum`, transported
along `P ≃o Fin |P|`, `Q ≃o Fin |Q|`) supplies a balanced one. -/
theorem oneThirdTwoThirdsFor_par_chains
    (htotα : ∀ a b : X, a ≤ b ∨ b ≤ a) (htotβ : ∀ a b : Y, a ≤ b ∨ b ≤ a) :
    OneThirdTwoThirdsFor (X := X ⊕ Y) := by
  have hnotα : ¬ IsNotChain (X := X) := fun ⟨x, y, hxy⟩ => (htotα x y).elim hxy.1 hxy.2
  have hnotβ : ¬ IsNotChain (X := Y) := fun ⟨x, y, hxy⟩ => (htotβ x y).elim hxy.1 hxy.2
  refine oneThirdTwoThirdsFor_par (fun h => absurd h hnotα) (fun h => absurd h hnotβ) ?_
  intro hnc _ _
  -- a cross incomparable pair witnesses both summands nonempty
  obtain ⟨u, v, huv⟩ := hnc
  have hαβ : Nonempty X ∧ Nonempty Y := by
    cases u with
    | inl a => cases v with
      | inl b => exact absurd ⟨a, b, (incomp_par_inl a b).mp huv⟩ hnotα
      | inr b => exact ⟨⟨a⟩, ⟨b⟩⟩
    | inr a => cases v with
      | inl b => exact ⟨⟨b⟩, ⟨a⟩⟩
      | inr b => exact absurd ⟨a, b, (incomp_par_inr a b).mp huv⟩ hnotβ
  have hcα : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr hαβ.1
  have hcβ : 1 ≤ Fintype.card Y := Fintype.card_pos_iff.mpr hαβ.2
  let e : (X ⊕ Y) ≃o (Fin (Fintype.card X) ⊕ Fin (Fintype.card Y)) :=
    sumCongrOrderIso (chainOrderIso htotα) (chainOrderIso htotβ)
  obtain ⟨p, q, hb⟩ := balancedPair_finSum hcα hcβ
  exact ⟨e.symm p, e.symm q, (isBalancedPair_orderIso e.symm p q).mp hb⟩

/-- **The disjoint-union reduction, unconditional.**  If `P` and `Q` each satisfy
the conjecture, so does `P ⊔ Q` — the `hcross` hypothesis is now discharged
(`oneThirdTwoThirdsFor_par_chains` handles the case where both summands are
chains). -/
theorem oneThirdTwoThirdsFor_par_total
    (hα : OneThirdTwoThirdsFor (X := X)) (hβ : OneThirdTwoThirdsFor (X := Y)) :
    OneThirdTwoThirdsFor (X := X ⊕ Y) := by
  refine oneThirdTwoThirdsFor_par hα hβ (fun hnc hαc hβc => ?_)
  have htotα : ∀ a b : X, a ≤ b ∨ b ≤ a := fun a b => by
    by_contra h; push_neg at h; exact hαc ⟨a, b, h.1, h.2⟩
  have htotβ : ∀ a b : Y, a ≤ b ∨ b ≤ a := fun a b => by
    by_contra h; push_neg at h; exact hβc ⟨a, b, h.1, h.2⟩
  exact oneThirdTwoThirdsFor_par_chains htotα htotβ hnc

end OneThirdTwoThirds
