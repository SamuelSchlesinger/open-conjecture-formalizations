import OneThirdTwoThirds.DisjointUnion
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# The 1/3–2/3 conjecture — the disjoint-union (parallel) reduction

The **disjoint union** (parallel composition) `P ⊔ Q` keeps the two summands
incomparable (`DisjointUnion.instPartialOrderSum`).  A linear extension of
`P ⊔ Q` is a *shuffle*: it chooses which `|P|` of the `|P|+|Q|` positions carry
the `P`-elements (an arbitrary `m`-subset `S`, unlike the ordinal sum where `P`
is forced to the bottom block), then linearly extends each summand into its
positions.  This gives a bijection

```
linExts (P ⊔ Q)  ≃  linExts P  ×  {m-subsets of positions}  ×  linExts Q
```

and hence the classical **shuffle formula**
`e(P ⊔ Q) = C(|P|+|Q|, |P|) · e(P) · e(Q)` (`numLinExts_par`), together with
`e(P ⊔ Q, ↑x<↑y) = e(P, x<y) · C(…) · e(Q)` (`numBefore_par_inl`).  The common
factor `C(…)·e(Q)` cancels, so **every internal pair keeps its balance**
(`isBalancedPair_par_inl`/`_inr`).

Consequently, if a summand is *not a chain*, its balanced pair survives in the
union: `oneThirdTwoThirdsFor_par_of_left`/`_right`.  Combined with the ordinal-sum
reduction (`OrdinalSum`) this proves the conjecture for series-parallel posets
*except* the case where **both** summands are chains and the witnessing pair must
be a cross pair `{↑x, ↑y'}` — that residual case needs a separate
intermediate-value argument on the `δ`-values and is documented, not formalized,
here.

The crux is the *order-iso reindexing* `Finset.orderIsoOfFin` / `orderEmbOfFin`
of the varying position-subset `S`.  `sorry`-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OneThirdTwoThirds

open Finset

variable {α β : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableLE α]
  [Fintype β] [DecidableEq β] [PartialOrder β] [DecidableLE β]

/-- `inl`-elements are ordered exactly as in `α`. -/
theorem par_inl_le_inl (a b : α) : (Sum.inl a : α ⊕ β) ≤ Sum.inl b ↔ a ≤ b := Iff.rfl

/-- `inr`-elements are ordered exactly as in `β`. -/
theorem par_inr_le_inr (a b : β) : (Sum.inr a : α ⊕ β) ≤ Sum.inr b ↔ a ≤ b := Iff.rfl

theorem card_par : Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β := Fintype.card_sum

/-- A small congruence lemma: `orderEmbOfFin` only depends on the finset (and the
index), not the cardinality proof — so equal finsets give equal embeddings. -/
theorem orderEmbOfFin_congr {X : Type*} [LinearOrder X] {s t : Finset X} (hst : s = t)
    {k : ℕ} (hs : s.card = k) (ht : t.card = k) (i : Fin k) :
    s.orderEmbOfFin hs i = t.orderEmbOfFin ht i := by
  subst hst; rfl

/-! ### The position-subset carried by the `P`-block -/

/-- The set of positions occupied by the `inl` (i.e. `P`) elements in a ranking
`F` of `P ⊔ Q`. -/
def posSet (F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))) : Finset (Fin (Fintype.card (α ⊕ β))) :=
  Finset.univ.image (fun a : α => F (Sum.inl a))

theorem mem_posSet (F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))) (a : α) :
    F (Sum.inl a) ∈ posSet F :=
  Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

theorem posSet_card {F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))} (hinj : Function.Injective F) :
    (posSet F).card = Fintype.card α := by
  unfold posSet
  rw [Finset.card_image_of_injective _ (fun x y h => Sum.inl_injective (hinj h)),
    Finset.card_univ]

theorem notMem_posSet {F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))} (hinj : Function.Injective F)
    (b : β) : F (Sum.inr b) ∉ posSet F := by
  intro hmem
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmem
  exact Sum.inl_ne_inr (hinj ha)

theorem mem_compl_posSet {F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))} (hinj : Function.Injective F)
    (b : β) : F (Sum.inr b) ∈ (posSet F)ᶜ :=
  Finset.mem_compl.mpr (notMem_posSet hinj b)

theorem compl_posSet_card {F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))}
    (hinj : Function.Injective F) : (posSet F)ᶜ.card = Fintype.card β := by
  rw [Finset.card_compl, Fintype.card_fin, posSet_card hinj]
  have := card_par (α := α) (β := β); omega

/-! ### Restricting a ranking to each block -/

/-- The induced ranking of `P`: the rank of `F (inl a)` within the position-set. -/
def restrictParL (F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β)))
    (hc : (posSet F).card = Fintype.card α) : α → Fin (Fintype.card α) :=
  fun a => (Finset.orderIsoOfFin (posSet F) hc).symm ⟨F (Sum.inl a), mem_posSet F a⟩

/-- The induced ranking of `Q`. -/
def restrictParR (F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β)))
    (hinj : Function.Injective F) (hc : (posSet F)ᶜ.card = Fintype.card β) : β → Fin (Fintype.card β) :=
  fun b => (Finset.orderIsoOfFin (posSet F)ᶜ hc).symm ⟨F (Sum.inr b), mem_compl_posSet hinj b⟩

/-- Defining property: embedding the rank back recovers the position. -/
theorem restrictParL_spec (F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β)))
    (hc : (posSet F).card = Fintype.card α) (a : α) :
    (posSet F).orderEmbOfFin hc (restrictParL F hc a) = F (Sum.inl a) := by
  unfold restrictParL
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem restrictParR_spec (F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β)))
    (hinj : Function.Injective F) (hc : (posSet F)ᶜ.card = Fintype.card β) (b : β) :
    (posSet F)ᶜ.orderEmbOfFin hc (restrictParR F hinj hc b) = F (Sum.inr b) := by
  unfold restrictParR
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem isLinExt_restrictParL {F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))} (hF : IsLinExt F)
    (hc : (posSet F).card = Fintype.card α) : IsLinExt (restrictParL F hc) := by
  obtain ⟨hinj, hmono⟩ := hF
  refine ⟨?_, ?_⟩
  · intro a b hab
    have : F (Sum.inl a) = F (Sum.inl b) := by
      rw [← restrictParL_spec F hc a, ← restrictParL_spec F hc b, hab]
    exact Sum.inl_injective (hinj this)
  · intro a b hab
    have hle : F (Sum.inl a) ≤ F (Sum.inl b) := hmono _ _ ((par_inl_le_inl a b).mpr hab)
    have key : (posSet F).orderEmbOfFin hc (restrictParL F hc a)
        ≤ (posSet F).orderEmbOfFin hc (restrictParL F hc b) := by
      rw [restrictParL_spec F hc a, restrictParL_spec F hc b]; exact hle
    exact (Finset.orderEmbOfFin (posSet F) hc).le_iff_le.mp key

theorem isLinExt_restrictParR {F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))} (hF : IsLinExt F)
    (hc : (posSet F)ᶜ.card = Fintype.card β) : IsLinExt (restrictParR F hF.1 hc) := by
  obtain ⟨hinj, hmono⟩ := hF
  refine ⟨?_, ?_⟩
  · intro a b hab
    have : F (Sum.inr a) = F (Sum.inr b) := by
      rw [← restrictParR_spec F hinj hc a, ← restrictParR_spec F hinj hc b, hab]
    exact Sum.inr_injective (hinj this)
  · intro a b hab
    have hle : F (Sum.inr a) ≤ F (Sum.inr b) := hmono _ _ ((par_inr_le_inr a b).mpr hab)
    have key : (posSet F)ᶜ.orderEmbOfFin hc (restrictParR F hinj hc a)
        ≤ (posSet F)ᶜ.orderEmbOfFin hc (restrictParR F hinj hc b) := by
      rw [restrictParR_spec F hinj hc a, restrictParR_spec F hinj hc b]; exact hle
    exact (Finset.orderEmbOfFin (posSet F)ᶜ hc).le_iff_le.mp key

/-! ### Reassembling a ranking from a subset and two block-rankings -/

/-- Reconstruct a ranking of `P ⊔ Q` from a position-set `S` (of size `|P|`) and
rankings `g, h` of the two blocks: place `inl a` at the `(g a)`-th element of `S`
and `inr b` at the `(h b)`-th element of `Sᶜ`. -/
def combinePar (S : Finset (Fin (Fintype.card (α ⊕ β)))) (hS : S.card = Fintype.card α)
    (hSc : Sᶜ.card = Fintype.card β) (g : α → Fin (Fintype.card α))
    (h : β → Fin (Fintype.card β)) : (α ⊕ β) → Fin (Fintype.card (α ⊕ β)) :=
  fun z => match z with
    | Sum.inl a => S.orderEmbOfFin hS (g a)
    | Sum.inr b => Sᶜ.orderEmbOfFin hSc (h b)

@[simp] theorem combinePar_inl (S : Finset (Fin (Fintype.card (α ⊕ β))))
    (hS : S.card = Fintype.card α) (hSc : Sᶜ.card = Fintype.card β)
    (g : α → Fin (Fintype.card α)) (h : β → Fin (Fintype.card β)) (a : α) :
    combinePar S hS hSc g h (Sum.inl a) = S.orderEmbOfFin hS (g a) := rfl

@[simp] theorem combinePar_inr (S : Finset (Fin (Fintype.card (α ⊕ β))))
    (hS : S.card = Fintype.card α) (hSc : Sᶜ.card = Fintype.card β)
    (g : α → Fin (Fintype.card α)) (h : β → Fin (Fintype.card β)) (b : β) :
    combinePar S hS hSc g h (Sum.inr b) = Sᶜ.orderEmbOfFin hSc (h b) := rfl

theorem posSet_combinePar {S : Finset (Fin (Fintype.card (α ⊕ β)))}
    {hS : S.card = Fintype.card α} {hSc : Sᶜ.card = Fintype.card β}
    {g : α → Fin (Fintype.card α)} {h : β → Fin (Fintype.card β)} (hg : Function.Surjective g) :
    posSet (combinePar S hS hSc g h) = S := by
  unfold posSet
  simp only [combinePar_inl]
  have e1 : (Finset.univ.image fun a => S.orderEmbOfFin hS (g a))
      = (Finset.univ.image g).image (S.orderEmbOfFin hS) := (Finset.image_image).symm
  have e2 : Finset.univ.image g = (Finset.univ : Finset (Fin (Fintype.card α))) := by
    refine Finset.eq_univ_iff_forall.mpr (fun y => ?_)
    obtain ⟨x, hx⟩ := hg y
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩
  rw [e1, e2, Finset.image_orderEmbOfFin_univ]

theorem compl_card_eq {S : Finset (Fin (Fintype.card (α ⊕ β)))}
    (hS : S.card = Fintype.card α) : Sᶜ.card = Fintype.card β := by
  rw [Finset.card_compl, Fintype.card_fin, hS]
  have := card_par (α := α) (β := β); omega

theorem linExt_surjective {γ : Type*} [Fintype γ] {g : γ → Fin (Fintype.card γ)}
    (hg : Function.Injective g) : Function.Surjective g :=
  ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, (Fintype.card_fin _).symm⟩).surjective

theorem isLinExt_combinePar {S : Finset (Fin (Fintype.card (α ⊕ β)))}
    {hS : S.card = Fintype.card α} {hSc : Sᶜ.card = Fintype.card β}
    {g : α → Fin (Fintype.card α)} {h : β → Fin (Fintype.card β)}
    (hg : IsLinExt g) (hh : IsLinExt h) : IsLinExt (combinePar S hS hSc g h) := by
  obtain ⟨hginj, hgmono⟩ := hg
  obtain ⟨hhinj, hhmono⟩ := hh
  refine ⟨?_, ?_⟩
  · intro z w hzw
    cases z with
    | inl a => cases w with
      | inl b =>
        simp only [combinePar_inl] at hzw
        exact congrArg Sum.inl (hginj ((Finset.orderEmbOfFin S hS).injective hzw))
      | inr b =>
        exfalso
        have hmemS : combinePar S hS hSc g h (Sum.inl a) ∈ S := by
          rw [combinePar_inl]; exact Finset.orderEmbOfFin_mem _ _ _
        have hmemSc : combinePar S hS hSc g h (Sum.inr b) ∈ Sᶜ := by
          rw [combinePar_inr]; exact Finset.orderEmbOfFin_mem _ _ _
        rw [hzw] at hmemS
        exact (Finset.mem_compl.mp hmemSc) hmemS
    | inr a => cases w with
      | inl b =>
        exfalso
        have hmemSc : combinePar S hS hSc g h (Sum.inr a) ∈ Sᶜ := by
          rw [combinePar_inr]; exact Finset.orderEmbOfFin_mem _ _ _
        have hmemS : combinePar S hS hSc g h (Sum.inl b) ∈ S := by
          rw [combinePar_inl]; exact Finset.orderEmbOfFin_mem _ _ _
        rw [hzw] at hmemSc
        exact (Finset.mem_compl.mp hmemSc) hmemS
      | inr b =>
        simp only [combinePar_inr] at hzw
        exact congrArg Sum.inr (hhinj ((Finset.orderEmbOfFin Sᶜ hSc).injective hzw))
  · intro z w hzw
    cases z with
    | inl a => cases w with
      | inl b =>
        simp only [combinePar_inl]
        exact (Finset.orderEmbOfFin S hS).monotone (hgmono a b hzw)
      | inr b => exact hzw.elim
    | inr a => cases w with
      | inl b => exact hzw.elim
      | inr b =>
        simp only [combinePar_inr]
        exact (Finset.orderEmbOfFin Sᶜ hSc).monotone (hhmono a b hzw)

/-! ### Round-trip lemmas -/

theorem restrictParL_combinePar {S : Finset (Fin (Fintype.card (α ⊕ β)))}
    {hS : S.card = Fintype.card α} {hSc : Sᶜ.card = Fintype.card β}
    {g : α → Fin (Fintype.card α)} {h : β → Fin (Fintype.card β)} (hg : IsLinExt g)
    (hc : (posSet (combinePar S hS hSc g h)).card = Fintype.card α) :
    restrictParL (combinePar S hS hSc g h) hc = g := by
  funext a
  have hPS : posSet (combinePar S hS hSc g h) = S := posSet_combinePar (linExt_surjective hg.1)
  have key : S.orderEmbOfFin hS (restrictParL (combinePar S hS hSc g h) hc a)
      = S.orderEmbOfFin hS (g a) := by
    rw [← orderEmbOfFin_congr hPS hc hS (restrictParL (combinePar S hS hSc g h) hc a),
      restrictParL_spec (combinePar S hS hSc g h) hc a, combinePar_inl]
  exact Fin.ext (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mp key)

theorem restrictParR_combinePar {S : Finset (Fin (Fintype.card (α ⊕ β)))}
    {hS : S.card = Fintype.card α} {hSc : Sᶜ.card = Fintype.card β}
    {g : α → Fin (Fintype.card α)} {h : β → Fin (Fintype.card β)} (hg : IsLinExt g)
    (hinj : Function.Injective (combinePar S hS hSc g h))
    (hc : (posSet (combinePar S hS hSc g h))ᶜ.card = Fintype.card β) :
    restrictParR (combinePar S hS hSc g h) hinj hc = h := by
  funext b
  have hPSc : (posSet (combinePar S hS hSc g h))ᶜ = Sᶜ := by
    rw [posSet_combinePar (linExt_surjective hg.1)]
  have key : Sᶜ.orderEmbOfFin hSc (restrictParR (combinePar S hS hSc g h) hinj hc b)
      = Sᶜ.orderEmbOfFin hSc (h b) := by
    rw [← orderEmbOfFin_congr hPSc hc hSc (restrictParR (combinePar S hS hSc g h) hinj hc b),
      restrictParR_spec (combinePar S hS hSc g h) hinj hc b, combinePar_inr]
  exact Fin.ext (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mp key)

theorem combinePar_restrictPar {F : (α ⊕ β) → Fin (Fintype.card (α ⊕ β))} (hF : IsLinExt F) :
    combinePar (posSet F) (posSet_card hF.1) (compl_posSet_card hF.1)
      (restrictParL F (posSet_card hF.1)) (restrictParR F hF.1 (compl_posSet_card hF.1)) = F := by
  funext z
  cases z with
  | inl a =>
    rw [combinePar_inl, restrictParL_spec F (posSet_card hF.1) a]
  | inr b =>
    rw [combinePar_inr, restrictParR_spec F hF.1 (compl_posSet_card hF.1) b]

/-! ### The shuffle count and before-counts -/

/-- The number of position-subsets, `C(|P|+|Q|, |P|)`. -/
abbrev shuffleCount : ℕ :=
  ((Finset.univ : Finset (Fin (Fintype.card (α ⊕ β)))).powersetCard (Fintype.card α)).card

/-- **The shuffle formula** `e(P ⊔ Q) = C(|P|+|Q|, |P|) · e(P) · e(Q)`, packaged
as `e(P) · (C · e(Q))` for the balance cancellation. -/
theorem numLinExts_par :
    numLinExts (X := α ⊕ β)
      = numLinExts (X := α) * (shuffleCount (α := α) (β := β) * numLinExts (X := β)) := by
  classical
  have hbij : numLinExts (X := α ⊕ β)
      = ((linExts (X := α)) ×ˢ
          (((Finset.univ : Finset (Fin (Fintype.card (α ⊕ β)))).powersetCard (Fintype.card α))
            ×ˢ (linExts (X := β)))).card := by
    unfold numLinExts
    refine Finset.card_bij
      (fun F hF => (restrictParL F (posSet_card (mem_linExts.mp hF).1),
        (posSet F, restrictParR F (mem_linExts.mp hF).1 (compl_posSet_card (mem_linExts.mp hF).1))))
      ?_ ?_ ?_
    · intro F hF
      have hL := mem_linExts.mp hF
      rw [Finset.mem_product, Finset.mem_product]
      refine ⟨mem_linExts.mpr (isLinExt_restrictParL hL (posSet_card hL.1)), ?_,
        mem_linExts.mpr (isLinExt_restrictParR hL (compl_posSet_card hL.1))⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, posSet_card hL.1⟩
    · intro F₁ hF₁ F₂ hF₂ heq
      have hgL : restrictParL F₁ (posSet_card (mem_linExts.mp hF₁).1)
          = restrictParL F₂ (posSet_card (mem_linExts.mp hF₂).1) := congrArg Prod.fst heq
      have hPS : posSet F₁ = posSet F₂ := congrArg (fun t => (Prod.snd t).1) heq
      have hRR : restrictParR F₁ (mem_linExts.mp hF₁).1 (compl_posSet_card (mem_linExts.mp hF₁).1)
          = restrictParR F₂ (mem_linExts.mp hF₂).1 (compl_posSet_card (mem_linExts.mp hF₂).1) :=
        congrArg (fun t => (Prod.snd t).2) heq
      funext z
      cases z with
      | inl a =>
        rw [← restrictParL_spec F₁ (posSet_card (mem_linExts.mp hF₁).1) a,
          ← restrictParL_spec F₂ (posSet_card (mem_linExts.mp hF₂).1) a,
          orderEmbOfFin_congr hPS (posSet_card (mem_linExts.mp hF₁).1)
            (posSet_card (mem_linExts.mp hF₂).1), congrFun hgL a]
      | inr b =>
        have hPSc : (posSet F₁)ᶜ = (posSet F₂)ᶜ := by rw [hPS]
        rw [← restrictParR_spec F₁ (mem_linExts.mp hF₁).1 (compl_posSet_card (mem_linExts.mp hF₁).1) b,
          ← restrictParR_spec F₂ (mem_linExts.mp hF₂).1 (compl_posSet_card (mem_linExts.mp hF₂).1) b,
          orderEmbOfFin_congr hPSc (compl_posSet_card (mem_linExts.mp hF₁).1)
            (compl_posSet_card (mem_linExts.mp hF₂).1),
          congrFun hRR b]
    · intro p hp
      rw [Finset.mem_product, Finset.mem_product] at hp
      obtain ⟨hg, hS, hh⟩ := hp
      rw [Finset.mem_powersetCard] at hS
      have hScard := hS.2
      have hgL := mem_linExts.mp hg
      have hhL := mem_linExts.mp hh
      refine ⟨combinePar p.2.1 hScard (compl_card_eq hScard) p.1 p.2.2,
        mem_linExts.mpr (isLinExt_combinePar hgL hhL), ?_⟩
      refine Prod.ext (restrictParL_combinePar hgL _) (Prod.ext ?_ ?_)
      · exact posSet_combinePar (linExt_surjective hgL.1)
      · exact restrictParR_combinePar hgL (isLinExt_combinePar hgL hhL).1 _
  rw [hbij, Finset.card_product, Finset.card_product]
  rfl

/-- **The before-count of a bottom-block pair:** `e(P⊔Q, ↑x<↑y) = e(P,x<y) · C · e(Q)`.
The relative order of two `P`-elements is governed entirely by the `P`-ranking,
so the shuffle factor and `e(Q)` pass through untouched. -/
theorem numBefore_par_inl (x y : α) :
    numBefore (X := α ⊕ β) (Sum.inl x) (Sum.inl y)
      = numBefore (X := α) x y * (shuffleCount (α := α) (β := β) * numLinExts (X := β)) := by
  classical
  have hbij : numBefore (X := α ⊕ β) (Sum.inl x) (Sum.inl y)
      = (((linExts (X := α)).filter (fun g => g x < g y)) ×ˢ
          (((Finset.univ : Finset (Fin (Fintype.card (α ⊕ β)))).powersetCard (Fintype.card α))
            ×ˢ (linExts (X := β)))).card := by
    unfold numBefore
    refine Finset.card_bij
      (fun F hF =>
        (restrictParL F (posSet_card (mem_linExts.mp (Finset.mem_filter.mp hF).1).1),
          (posSet F, restrictParR F (mem_linExts.mp (Finset.mem_filter.mp hF).1).1
            (compl_posSet_card (mem_linExts.mp (Finset.mem_filter.mp hF).1).1))))
      ?_ ?_ ?_
    · intro F hF
      have hL := mem_linExts.mp (Finset.mem_filter.mp hF).1
      have hlt := (Finset.mem_filter.mp hF).2
      rw [Finset.mem_product, Finset.mem_product]
      refine ⟨Finset.mem_filter.mpr ⟨mem_linExts.mpr (isLinExt_restrictParL hL (posSet_card hL.1)),
        ?_⟩, ?_, mem_linExts.mpr (isLinExt_restrictParR hL (compl_posSet_card hL.1))⟩
      · have hkey : (posSet F).orderEmbOfFin (posSet_card hL.1)
              (restrictParL F (posSet_card hL.1) x)
            < (posSet F).orderEmbOfFin (posSet_card hL.1) (restrictParL F (posSet_card hL.1) y) := by
          rw [restrictParL_spec F (posSet_card hL.1) x, restrictParL_spec F (posSet_card hL.1) y]
          exact hlt
        exact (Finset.orderEmbOfFin (posSet F) (posSet_card hL.1)).lt_iff_lt.mp hkey
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, posSet_card hL.1⟩
    · intro F₁ hF₁ F₂ hF₂ heq
      set j₁ := (mem_linExts.mp (Finset.mem_filter.mp hF₁).1).1 with hj₁
      set j₂ := (mem_linExts.mp (Finset.mem_filter.mp hF₂).1).1 with hj₂
      have hgL : restrictParL F₁ (posSet_card j₁) = restrictParL F₂ (posSet_card j₂) :=
        congrArg Prod.fst heq
      have hPS : posSet F₁ = posSet F₂ := congrArg (fun t => (Prod.snd t).1) heq
      have hRR : restrictParR F₁ j₁ (compl_posSet_card j₁)
          = restrictParR F₂ j₂ (compl_posSet_card j₂) := congrArg (fun t => (Prod.snd t).2) heq
      funext z
      cases z with
      | inl a =>
        rw [← restrictParL_spec F₁ (posSet_card j₁) a, ← restrictParL_spec F₂ (posSet_card j₂) a,
          orderEmbOfFin_congr hPS (posSet_card j₁) (posSet_card j₂), congrFun hgL a]
      | inr b =>
        have hPSc : (posSet F₁)ᶜ = (posSet F₂)ᶜ := by rw [hPS]
        rw [← restrictParR_spec F₁ j₁ (compl_posSet_card j₁) b,
          ← restrictParR_spec F₂ j₂ (compl_posSet_card j₂) b,
          orderEmbOfFin_congr hPSc (compl_posSet_card j₁) (compl_posSet_card j₂), congrFun hRR b]
    · intro p hp
      rw [Finset.mem_product, Finset.mem_product] at hp
      obtain ⟨hg, hS, hh⟩ := hp
      rw [Finset.mem_filter] at hg
      rw [Finset.mem_powersetCard] at hS
      have hScard := hS.2
      have hgL := mem_linExts.mp hg.1
      have hhL := mem_linExts.mp hh
      refine ⟨combinePar p.2.1 hScard (compl_card_eq hScard) p.1 p.2.2,
        Finset.mem_filter.mpr ⟨mem_linExts.mpr (isLinExt_combinePar hgL hhL), ?_⟩, ?_⟩
      · rw [combinePar_inl, combinePar_inl]
        exact (Finset.orderEmbOfFin p.2.1 hScard).strictMono hg.2
      · refine Prod.ext (restrictParL_combinePar hgL _) (Prod.ext ?_ ?_)
        · exact posSet_combinePar (linExt_surjective hgL.1)
        · exact restrictParR_combinePar hgL (isLinExt_combinePar hgL hhL).1 _
  rw [hbij, Finset.card_product, Finset.card_product]
  rfl

/-- **The before-count of a top-block pair:** `e(P⊔Q, ↑x<↑y) = e(P) · C · e(Q,x<y)`. -/
theorem numBefore_par_inr (x y : β) :
    numBefore (X := α ⊕ β) (Sum.inr x) (Sum.inr y)
      = numLinExts (X := α) * (shuffleCount (α := α) (β := β) * numBefore (X := β) x y) := by
  classical
  have hbij : numBefore (X := α ⊕ β) (Sum.inr x) (Sum.inr y)
      = ((linExts (X := α)) ×ˢ
          (((Finset.univ : Finset (Fin (Fintype.card (α ⊕ β)))).powersetCard (Fintype.card α))
            ×ˢ ((linExts (X := β)).filter (fun h => h x < h y)))).card := by
    unfold numBefore
    refine Finset.card_bij
      (fun F hF =>
        (restrictParL F (posSet_card (mem_linExts.mp (Finset.mem_filter.mp hF).1).1),
          (posSet F, restrictParR F (mem_linExts.mp (Finset.mem_filter.mp hF).1).1
            (compl_posSet_card (mem_linExts.mp (Finset.mem_filter.mp hF).1).1))))
      ?_ ?_ ?_
    · intro F hF
      have hL := mem_linExts.mp (Finset.mem_filter.mp hF).1
      have hlt := (Finset.mem_filter.mp hF).2
      rw [Finset.mem_product, Finset.mem_product]
      refine ⟨mem_linExts.mpr (isLinExt_restrictParL hL (posSet_card hL.1)), ?_,
        Finset.mem_filter.mpr ⟨mem_linExts.mpr (isLinExt_restrictParR hL (compl_posSet_card hL.1)),
          ?_⟩⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, posSet_card hL.1⟩
      · have hkey : (posSet F)ᶜ.orderEmbOfFin (compl_posSet_card hL.1)
              (restrictParR F hL.1 (compl_posSet_card hL.1) x)
            < (posSet F)ᶜ.orderEmbOfFin (compl_posSet_card hL.1)
              (restrictParR F hL.1 (compl_posSet_card hL.1) y) := by
          rw [restrictParR_spec F hL.1 (compl_posSet_card hL.1) x,
            restrictParR_spec F hL.1 (compl_posSet_card hL.1) y]
          exact hlt
        exact (Finset.orderEmbOfFin (posSet F)ᶜ (compl_posSet_card hL.1)).lt_iff_lt.mp hkey
    · intro F₁ hF₁ F₂ hF₂ heq
      set j₁ := (mem_linExts.mp (Finset.mem_filter.mp hF₁).1).1 with hj₁
      set j₂ := (mem_linExts.mp (Finset.mem_filter.mp hF₂).1).1 with hj₂
      have hgL : restrictParL F₁ (posSet_card j₁) = restrictParL F₂ (posSet_card j₂) :=
        congrArg Prod.fst heq
      have hPS : posSet F₁ = posSet F₂ := congrArg (fun t => (Prod.snd t).1) heq
      have hRR : restrictParR F₁ j₁ (compl_posSet_card j₁)
          = restrictParR F₂ j₂ (compl_posSet_card j₂) := congrArg (fun t => (Prod.snd t).2) heq
      funext z
      cases z with
      | inl a =>
        rw [← restrictParL_spec F₁ (posSet_card j₁) a, ← restrictParL_spec F₂ (posSet_card j₂) a,
          orderEmbOfFin_congr hPS (posSet_card j₁) (posSet_card j₂), congrFun hgL a]
      | inr b =>
        have hPSc : (posSet F₁)ᶜ = (posSet F₂)ᶜ := by rw [hPS]
        rw [← restrictParR_spec F₁ j₁ (compl_posSet_card j₁) b,
          ← restrictParR_spec F₂ j₂ (compl_posSet_card j₂) b,
          orderEmbOfFin_congr hPSc (compl_posSet_card j₁) (compl_posSet_card j₂), congrFun hRR b]
    · intro p hp
      rw [Finset.mem_product, Finset.mem_product] at hp
      obtain ⟨hg, hS, hh⟩ := hp
      rw [Finset.mem_filter] at hh
      rw [Finset.mem_powersetCard] at hS
      have hScard := hS.2
      have hgL := mem_linExts.mp hg
      have hhL := mem_linExts.mp hh.1
      refine ⟨combinePar p.2.1 hScard (compl_card_eq hScard) p.1 p.2.2,
        Finset.mem_filter.mpr ⟨mem_linExts.mpr (isLinExt_combinePar hgL hhL), ?_⟩, ?_⟩
      · rw [combinePar_inr, combinePar_inr]
        exact (Finset.orderEmbOfFin (p.2.1)ᶜ (compl_card_eq hScard)).strictMono hh.2
      · refine Prod.ext (restrictParL_combinePar hgL _) (Prod.ext ?_ ?_)
        · exact posSet_combinePar (linExt_surjective hgL.1)
        · exact restrictParR_combinePar hgL (isLinExt_combinePar hgL hhL).1 _
  rw [hbij, Finset.card_product, Finset.card_product]
  rfl

/-- The explicit shuffle formula `e(P ⊔ Q) = C(|P|+|Q|, |P|) · e(P) · e(Q)`. -/
theorem numLinExts_par_eq_choose :
    numLinExts (X := α ⊕ β)
      = (Fintype.card α + Fintype.card β).choose (Fintype.card α)
        * numLinExts (X := α) * numLinExts (X := β) := by
  rw [numLinExts_par]
  unfold shuffleCount
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, card_par]
  ring

theorem shuffleCount_pos : 0 < shuffleCount (α := α) (β := β) := by
  unfold shuffleCount
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.choose_pos (by have := card_par (α := α) (β := β); omega)

private theorem mul_cancel {a b c : ℕ} (hc : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
  ⟨fun h => Nat.le_of_mul_le_mul_right h hc, fun h => by gcongr⟩

/-! ### Balance transfer and the reduction -/

/-- Incomparable bottom-block pairs correspond to incomparable pairs of `P`. -/
theorem incomp_par_inl (x y : α) :
    Incomp (X := α ⊕ β) (Sum.inl x) (Sum.inl y) ↔ Incomp (X := α) x y := by
  simp only [Incomp, par_inl_le_inl]

/-- Incomparable top-block pairs correspond to incomparable pairs of `Q`. -/
theorem incomp_par_inr (x y : β) :
    Incomp (X := α ⊕ β) (Sum.inr x) (Sum.inr y) ↔ Incomp (X := β) x y := by
  simp only [Incomp, par_inr_le_inr]

/-- **A disjoint union preserves balance of a bottom-block pair.** -/
theorem isBalancedPair_par_inl (x y : α) :
    IsBalancedPair (X := α ⊕ β) (Sum.inl x) (Sum.inl y) ↔ IsBalancedPair (X := α) x y := by
  have hc : 0 < shuffleCount (α := α) (β := β) * numLinExts (X := β) :=
    Nat.mul_pos shuffleCount_pos numLinExts_pos
  unfold IsBalancedPair
  rw [numBefore_par_inl, numLinExts_par, incomp_par_inl,
    show 3 * (numBefore (X := α) x y * (shuffleCount (α := α) (β := β) * numLinExts (X := β)))
      = (3 * numBefore (X := α) x y) * (shuffleCount (α := α) (β := β) * numLinExts (X := β)) by ring,
    show 2 * (numLinExts (X := α) * (shuffleCount (α := α) (β := β) * numLinExts (X := β)))
      = (2 * numLinExts (X := α)) * (shuffleCount (α := α) (β := β) * numLinExts (X := β)) by ring,
    mul_cancel hc, mul_cancel hc]

/-- **A disjoint union preserves balance of a top-block pair.** -/
theorem isBalancedPair_par_inr (x y : β) :
    IsBalancedPair (X := α ⊕ β) (Sum.inr x) (Sum.inr y) ↔ IsBalancedPair (X := β) x y := by
  have hc : 0 < numLinExts (X := α) * shuffleCount (α := α) (β := β) :=
    Nat.mul_pos numLinExts_pos shuffleCount_pos
  unfold IsBalancedPair
  rw [numBefore_par_inr, numLinExts_par, incomp_par_inr,
    show numLinExts (X := α) * (shuffleCount (α := α) (β := β) * numLinExts (X := β))
      = numLinExts (X := β) * (numLinExts (X := α) * shuffleCount (α := α) (β := β)) by ring,
    show 3 * (numLinExts (X := α) * (shuffleCount (α := α) (β := β) * numBefore (X := β) x y))
      = (3 * numBefore (X := β) x y) * (numLinExts (X := α) * shuffleCount (α := α) (β := β)) by ring,
    show 2 * (numLinExts (X := β) * (numLinExts (X := α) * shuffleCount (α := α) (β := β)))
      = (2 * numLinExts (X := β)) * (numLinExts (X := α) * shuffleCount (α := α) (β := β)) by ring,
    mul_cancel hc, mul_cancel hc]

/-- **The disjoint-union reduction (modulo the two-chains case).**  If both
summands satisfy the conjecture *and* every disjoint union of two chains has a
balanced (cross) pair, then `P ⊔ Q` satisfies the conjecture.  The first two
hypotheses cover the case where some summand is not a chain (its balanced pair
lifts, by `isBalancedPair_par_inl`/`_inr`); the `hcross` hypothesis isolates the
genuinely harder case where **both** summands are chains, so the witness must be a
cross pair `{↑x, ↑y'}` — that is the real content of the series-parallel theorem
and requires an intermediate-value argument on the `δ`-values, not formalized
here. -/
theorem oneThirdTwoThirdsFor_par
    (hα : OneThirdTwoThirdsFor (X := α)) (hβ : OneThirdTwoThirdsFor (X := β))
    (hcross : IsNotChain (X := α ⊕ β) → ¬ IsNotChain (X := α) → ¬ IsNotChain (X := β) →
      ∃ u v : α ⊕ β, IsBalancedPair (X := α ⊕ β) u v) :
    OneThirdTwoThirdsFor (X := α ⊕ β) := by
  intro hnc
  by_cases hαc : IsNotChain (X := α)
  · obtain ⟨x, y, hb⟩ := hα hαc
    exact ⟨Sum.inl x, Sum.inl y, (isBalancedPair_par_inl x y).mpr hb⟩
  · by_cases hβc : IsNotChain (X := β)
    · obtain ⟨x, y, hb⟩ := hβ hβc
      exact ⟨Sum.inr x, Sum.inr y, (isBalancedPair_par_inr x y).mpr hb⟩
    · exact hcross hnc hαc hβc

/-- If `P` is not a chain, its balanced pair survives in `P ⊔ Q`, so `P ⊔ Q`
satisfies the conjecture (no cross-pair argument needed). -/
theorem oneThirdTwoThirdsFor_par_of_left
    (hα : OneThirdTwoThirdsFor (X := α)) (hnc : IsNotChain (X := α)) :
    OneThirdTwoThirdsFor (X := α ⊕ β) := by
  intro _
  obtain ⟨x, y, hb⟩ := hα hnc
  exact ⟨Sum.inl x, Sum.inl y, (isBalancedPair_par_inl x y).mpr hb⟩

/-- If `Q` is not a chain, its balanced pair survives in `P ⊔ Q`. -/
theorem oneThirdTwoThirdsFor_par_of_right
    (hβ : OneThirdTwoThirdsFor (X := β)) (hnc : IsNotChain (X := β)) :
    OneThirdTwoThirdsFor (X := α ⊕ β) := by
  intro _
  obtain ⟨x, y, hb⟩ := hβ hnc
  exact ⟨Sum.inr x, Sum.inr y, (isBalancedPair_par_inr x y).mpr hb⟩

end OneThirdTwoThirds
