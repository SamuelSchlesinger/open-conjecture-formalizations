import OneThirdTwoThirds.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

/-!
# The 1/3–2/3 conjecture — the ordinal sum reduction

The **ordinal sum** `P ⊕ Q` (here `Ser P Q`) stacks `Q` entirely above `P`: every
element of `P` is below every element of `Q`.  Its linear extensions are exactly
a linear extension of `P` followed by one of `Q` — no interleaving — so

```
e(P ⊕ Q)          = e(P) · e(Q)                       (numLinExts_ser)
e(P ⊕ Q, x<y)     = e(P, x<y) · e(Q)   for x,y ∈ P    (numBefore_ser_inl)
```

Hence `δ(x,y)` is identical in `P` and in `P ⊕ Q`, and the incomparable pairs of
`P ⊕ Q` are exactly those of `P` together with those of `Q` (there are no
cross-incomparabilities).  Therefore the conjecture for `P ⊕ Q` reduces to `P`
and `Q` (`oneThirdTwoThirdsFor_ser`): it suffices to verify the conjecture on
**ordinal-sum-indecomposable** posets.

The crux is the *forcing* lemma: in any linear extension of `P ⊕ Q`, the
`P`-elements occupy the bottom `|P|` positions (and `Q` the top `|Q|`), proved by
a pigeonhole on the `|Q|` elements that must sit above any given `P`-element.

`sorry`-free.
-/

set_option autoImplicit false
-- many lemmas below use only a subset of the eight ambient instances on `α, β`
set_option linter.unusedSectionVars false

namespace OneThirdTwoThirds

/-- The **ordinal sum** of two posets: `Q` stacked entirely above `P`. -/
def Ser (α β : Type*) : Type _ := α ⊕ β

namespace Ser

variable {α β : Type*}

instance [Fintype α] [Fintype β] : Fintype (Ser α β) := inferInstanceAs (Fintype (α ⊕ β))
instance [DecidableEq α] [DecidableEq β] : DecidableEq (Ser α β) :=
  inferInstanceAs (DecidableEq (α ⊕ β))

/-- Left injection into the ordinal sum (the bottom block). -/
@[match_pattern, reducible] def inl (a : α) : Ser α β := Sum.inl a
/-- Right injection into the ordinal sum (the top block). -/
@[match_pattern, reducible] def inr (b : β) : Ser α β := Sum.inr b

instance [PartialOrder α] [PartialOrder β] : PartialOrder (Ser α β) where
  le x y := match x, y with
    | Sum.inl a, Sum.inl b => a ≤ b
    | Sum.inr a, Sum.inr b => a ≤ b
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => False
  lt x y := match x, y with
    | Sum.inl a, Sum.inl b => a < b
    | Sum.inr a, Sum.inr b => a < b
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => False
  le_refl x := by cases x with | inl a => exact le_refl a | inr a => exact le_refl a
  le_trans x y z := by
    cases x <;> cases y <;> cases z <;> intro hxy hyz <;>
      first
        | exact le_trans hxy hyz
        | exact hxy.elim
        | exact hyz.elim
        | trivial
  le_antisymm x y := by
    cases x <;> cases y <;> intro hxy hyx <;>
      first
        | exact congrArg Sum.inl (le_antisymm hxy hyx)
        | exact congrArg Sum.inr (le_antisymm hxy hyx)
        | exact hxy.elim
        | exact hyx.elim
  lt_iff_le_not_ge x y := by
    cases x <;> cases y <;> first | exact lt_iff_le_not_ge | simp

instance [PartialOrder α] [PartialOrder β] [DecidableLE α] [DecidableLE β] :
    DecidableLE (Ser α β) := fun x y =>
  match x, y with
  | Sum.inl a, Sum.inl b => inferInstanceAs (Decidable (a ≤ b))
  | Sum.inr a, Sum.inr b => inferInstanceAs (Decidable (a ≤ b))
  | Sum.inl _, Sum.inr _ => isTrue trivial
  | Sum.inr _, Sum.inl _ => isFalse not_false

theorem card_ser [Fintype α] [Fintype β] :
    Fintype.card (Ser α β) = Fintype.card α + Fintype.card β := Fintype.card_sum

section Order
variable [PartialOrder α] [PartialOrder β]

@[simp] theorem inl_le_inl {a b : α} : (inl a : Ser α β) ≤ inl b ↔ a ≤ b := Iff.rfl
@[simp] theorem inr_le_inr {a b : β} : (inr a : Ser α β) ≤ inr b ↔ a ≤ b := Iff.rfl
theorem inl_le_inr (a : α) (b : β) : (inl a : Ser α β) ≤ inr b := trivial
@[simp] theorem not_inr_le_inl {a : α} {b : β} : ¬ (inr b : Ser α β) ≤ inl a := id
theorem inl_lt_inr (a : α) (b : β) : (inl a : Ser α β) < inr b := trivial

omit [PartialOrder α] [PartialOrder β] in
theorem inl_ne_inr (a : α) (b : β) : (inl a : Ser α β) ≠ inr b := Sum.inl_ne_inr

end Order

end Ser

open Ser

variable {α β : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableLE α]
  [Fintype β] [DecidableEq β] [PartialOrder β] [DecidableLE β]

omit [DecidableEq α] [DecidableLE α] [DecidableEq β] [DecidableLE β] in
/-- A linear extension of `P ⊕ Q`, viewed as a bijection, puts every `P`-element
strictly below every `Q`-element. -/
theorem linExt_inl_lt_inr {f : Ser α β → Fin (Fintype.card (Ser α β))} (hf : IsLinExt f)
    (a : α) (b : β) : f (Sum.inl a) < f (Sum.inr b) := by
  obtain ⟨hinj, hmono⟩ := hf
  exact lt_of_le_of_ne (hmono _ _ (Ser.inl_le_inr a b))
    (fun h => Sum.inl_ne_inr (hinj h))

omit [DecidableEq α] [DecidableLE α] [DecidableEq β] [DecidableLE β] in
/-- **Forcing (bottom block).**  In any linear extension of `P ⊕ Q`, each
`P`-element `Sum.inl a` occupies a position `< |P|`. -/
theorem forcingL {f : Ser α β → Fin (Fintype.card (Ser α β))} (hf : IsLinExt f) (a : α) :
    (f (Sum.inl a)).val < Fintype.card α := by
  obtain ⟨hinj, hmono⟩ := hf
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [Fintype.card_fin]⟩
  set v := f (Sum.inl a) with hv
  -- the `|Q|` elements `Sum.inr b` all map strictly above `v`
  have hup : Fintype.card β ≤
      (Finset.univ.filter (fun z => v < f z)).card := by
    classical
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun b => (Sum.inr b : Ser α β)) ?_ ?_
    · intro b _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact linExt_inl_lt_inr ⟨hinj, hmono⟩ a b
    · intro b₁ _ b₂ _ h; exact Sum.inr_injective h
  -- that count is `N - 1 - v.val` via the bijection `f`
  have hcount : (Finset.univ.filter (fun z => v < f z)).card = (Finset.Ioi v).card := by
    apply Finset.card_bij (fun z _ => f z)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simpa using hz
    · intro z₁ _ z₂ _ h; exact hbij.injective h
    · intro w hw
      simp only [Finset.mem_Ioi] at hw
      obtain ⟨z, rfl⟩ := hbij.surjective w
      exact ⟨z, by simp [hw], rfl⟩
  rw [hcount, Fin.card_Ioi] at hup
  have hvlt := v.isLt
  have hN := card_ser (α := α) (β := β)
  omega

/-- **Forcing (top block).**  Each `Q`-element `inr b` occupies a position
`≥ |P|`. -/
theorem forcingR {f : Ser α β → Fin (Fintype.card (Ser α β))} (hf : IsLinExt f) (b : β) :
    Fintype.card α ≤ (f (Sum.inr b)).val := by
  obtain ⟨hinj, hmono⟩ := hf
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [Fintype.card_fin]⟩
  set v := f (Sum.inr b) with hv
  -- the `|P|` elements `Sum.inl a` all map strictly below `v`
  have hdown : Fintype.card α ≤ (Finset.univ.filter (fun z => f z < v)).card := by
    classical
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun a => (Sum.inl a : Ser α β)) ?_ ?_
    · intro a _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact linExt_inl_lt_inr ⟨hinj, hmono⟩ a b
    · intro a₁ _ a₂ _ h; exact Sum.inl_injective h
  have hcount : (Finset.univ.filter (fun z => f z < v)).card = (Finset.Iio v).card := by
    apply Finset.card_bij (fun z _ => f z)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simpa using hz
    · intro z₁ _ z₂ _ h; exact hbij.injective h
    · intro w hw
      simp only [Finset.mem_Iio] at hw
      obtain ⟨z, rfl⟩ := hbij.surjective w
      exact ⟨z, by simp [hw], rfl⟩
  rw [hcount, Fin.card_Iio] at hdown
  exact hdown

/-! ### The linear-extension bijection -/

/-- Assemble a `Ser`-ranking from a ranking of each block: `P` fills the bottom
positions, `Q` the top ones (shifted by `|P|`). -/
def combine (g : α → Fin (Fintype.card α)) (h : β → Fin (Fintype.card β)) :
    Ser α β → Fin (Fintype.card (Ser α β)) := fun z =>
  match z with
  | Sum.inl a => ⟨(g a).val, by rw [card_ser]; have := (g a).isLt; omega⟩
  | Sum.inr b => ⟨Fintype.card α + (h b).val, by rw [card_ser]; have := (h b).isLt; omega⟩

omit [DecidableEq α] [PartialOrder α] [DecidableLE α] [DecidableEq β] [PartialOrder β] [DecidableLE β] in
@[simp] theorem combine_inl (g : α → Fin (Fintype.card α)) (h : β → Fin (Fintype.card β)) (a : α) :
    (combine g h (Sum.inl a)).val = (g a).val := rfl
omit [DecidableEq α] [PartialOrder α] [DecidableLE α] [DecidableEq β] [PartialOrder β] [DecidableLE β] in
@[simp] theorem combine_inr (g : α → Fin (Fintype.card α)) (h : β → Fin (Fintype.card β)) (b : β) :
    (combine g h (Sum.inr b)).val = Fintype.card α + (h b).val := rfl

omit [DecidableLE α] [DecidableLE β] in
theorem isLinExt_combine {g : α → Fin (Fintype.card α)} {h : β → Fin (Fintype.card β)}
    (hg : IsLinExt g) (hh : IsLinExt h) : IsLinExt (combine g h) := by
  obtain ⟨hgi, hgm⟩ := hg
  obtain ⟨hhi, hhm⟩ := hh
  refine ⟨?_, ?_⟩
  · intro z w hzw
    have hval := congrArg Fin.val hzw
    cases z with
    | inl a => cases w with
      | inl a' =>
        simp only [combine_inl] at hval
        exact congrArg Sum.inl (hgi (Fin.ext hval))
      | inr b' =>
        simp only [combine_inl, combine_inr] at hval
        have := (g a).isLt; omega
    | inr b => cases w with
      | inl a' =>
        simp only [combine_inl, combine_inr] at hval
        have := (g a').isLt; omega
      | inr b' =>
        simp only [combine_inr] at hval
        exact congrArg Sum.inr (hhi (Fin.ext (by omega)))
  · intro z w hzw
    cases z with
    | inl a => cases w with
      | inl a' =>
        refine Fin.le_def.mpr ?_
        simp only [combine_inl]
        exact Fin.le_def.mp (hgm a a' (Ser.inl_le_inl.mp hzw))
      | inr b' =>
        refine Fin.le_def.mpr ?_
        simp only [combine_inl, combine_inr]
        have := (g a).isLt; omega
    | inr b => cases w with
      | inl a' => exact (Ser.not_inr_le_inl hzw).elim
      | inr b' =>
        refine Fin.le_def.mpr ?_
        simp only [combine_inr]
        have := Fin.le_def.mp (hhm b b' (Ser.inr_le_inr.mp hzw))
        omega

/-- Restrict a `Ser`-ranking to its bottom block, a ranking of `P`. -/
def restrictL (f : Ser α β → Fin (Fintype.card (Ser α β))) (hf : IsLinExt f) :
    α → Fin (Fintype.card α) := fun a => ⟨(f (Sum.inl a)).val, forcingL hf a⟩

/-- Restrict a `Ser`-ranking to its top block, a ranking of `Q` (shifted down by
`|P|`). -/
def restrictR (f : Ser α β → Fin (Fintype.card (Ser α β))) (hf : IsLinExt f) :
    β → Fin (Fintype.card β) := fun b =>
  ⟨(f (Sum.inr b)).val - Fintype.card α, by
    have h1 := forcingR hf b
    have h2 := (f (Sum.inr b)).isLt
    have hN := card_ser (α := α) (β := β)
    omega⟩

@[simp] theorem restrictL_val (f : Ser α β → Fin (Fintype.card (Ser α β))) (hf : IsLinExt f)
    (a : α) : (restrictL f hf a).val = (f (Sum.inl a)).val := rfl
@[simp] theorem restrictR_val (f : Ser α β → Fin (Fintype.card (Ser α β))) (hf : IsLinExt f)
    (b : β) : (restrictR f hf b).val = (f (Sum.inr b)).val - Fintype.card α := rfl

theorem isLinExt_restrictL {f : Ser α β → Fin (Fintype.card (Ser α β))} (hf : IsLinExt f) :
    IsLinExt (restrictL f hf) := by
  refine ⟨?_, ?_⟩
  · intro a a' h
    have hval := congrArg Fin.val h
    simp only [restrictL_val] at hval
    exact Sum.inl_injective (hf.1 (Fin.ext hval))
  · intro a a' hab
    refine Fin.le_def.mpr ?_
    exact Fin.le_def.mp (hf.2 (Sum.inl a) (Sum.inl a') (Ser.inl_le_inl.mpr hab))

theorem isLinExt_restrictR {f : Ser α β → Fin (Fintype.card (Ser α β))} (hf : IsLinExt f) :
    IsLinExt (restrictR f hf) := by
  refine ⟨?_, ?_⟩
  · intro b b' h
    have hval := Fin.ext_iff.mp h
    change (f (Sum.inr b)).val - Fintype.card α
      = (f (Sum.inr b')).val - Fintype.card α at hval
    have h1 := forcingR hf b; have h2 := forcingR hf b'
    exact Sum.inr_injective (hf.1 (Fin.ext (by omega)))
  · intro b b' hab
    refine Fin.le_def.mpr ?_
    show (f (Sum.inr b)).val - Fintype.card α ≤ (f (Sum.inr b')).val - Fintype.card α
    have := Fin.le_def.mp (hf.2 (Sum.inr b) (Sum.inr b') (Ser.inr_le_inr.mpr hab))
    omega

/-- **The linear extensions of an ordinal sum multiply:** `e(P ⊕ Q) = e(P)·e(Q)`. -/
theorem numLinExts_ser :
    numLinExts (X := Ser α β) = numLinExts (X := α) * numLinExts (X := β) := by
  classical
  unfold numLinExts
  rw [← Finset.card_product]
  refine Finset.card_bij
    (fun f hf => (restrictL f (mem_linExts.mp hf), restrictR f (mem_linExts.mp hf)))
    ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_product]
    exact ⟨mem_linExts.mpr (isLinExt_restrictL (mem_linExts.mp hf)),
      mem_linExts.mpr (isLinExt_restrictR (mem_linExts.mp hf))⟩
  · intro f₁ hf₁ f₂ hf₂ heq
    have hL := congrArg Prod.fst heq
    have hR := congrArg Prod.snd heq
    funext z
    cases z with
    | inl a =>
      have hval := congrArg Fin.val (congrFun hL a)
      simp only [restrictL_val] at hval
      exact Fin.ext hval
    | inr b =>
      have hval := Fin.ext_iff.mp (congrFun hR b)
      change (f₁ (Sum.inr b)).val - Fintype.card α
        = (f₂ (Sum.inr b)).val - Fintype.card α at hval
      have h1 := forcingR (mem_linExts.mp hf₁) b
      have h2 := forcingR (mem_linExts.mp hf₂) b
      exact Fin.ext (by omega)
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hg, hh⟩ := hp
    refine ⟨combine p.1 p.2,
      mem_linExts.mpr (isLinExt_combine (mem_linExts.mp hg) (mem_linExts.mp hh)), ?_⟩
    refine Prod.ext ?_ ?_
    · funext a; refine Fin.ext ?_; simp only [restrictL_val, combine_inl]
    · funext b; refine Fin.ext ?_; simp only [restrictR_val, combine_inr]; omega

/-! ### The before-count splits, and the reduction -/

/-- **The before-count of a bottom-block pair multiplies:**
`e(P ⊕ Q, ↑x < ↑y) = e(P, x<y) · e(Q)` for `x, y ∈ P`. -/
theorem numBefore_ser_inl (x y : α) :
    numBefore (X := Ser α β) (Sum.inl x) (Sum.inl y)
      = numBefore (X := α) x y * numLinExts (X := β) := by
  classical
  unfold numBefore numLinExts
  rw [← Finset.card_product]
  refine Finset.card_bij
    (fun f hf => (restrictL f (mem_linExts.mp (Finset.mem_filter.mp hf).1),
                  restrictR f (mem_linExts.mp (Finset.mem_filter.mp hf).1))) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hmem, hlt⟩ := hf
    have hL := mem_linExts.mp hmem
    rw [Finset.mem_product, Finset.mem_filter]
    refine ⟨⟨mem_linExts.mpr (isLinExt_restrictL hL), ?_⟩,
      mem_linExts.mpr (isLinExt_restrictR hL)⟩
    refine Fin.lt_def.mpr ?_
    show (f (Sum.inl x)).val < (f (Sum.inl y)).val
    exact Fin.lt_def.mp hlt
  · intro f₁ hf₁ f₂ hf₂ heq
    rw [Finset.mem_filter] at hf₁ hf₂
    have hL := congrArg Prod.fst heq
    have hR := congrArg Prod.snd heq
    funext z
    cases z with
    | inl a =>
      have hval := congrArg Fin.val (congrFun hL a)
      simp only [restrictL_val] at hval
      exact Fin.ext hval
    | inr b =>
      have hval := Fin.ext_iff.mp (congrFun hR b)
      change (f₁ (Sum.inr b)).val - Fintype.card α
        = (f₂ (Sum.inr b)).val - Fintype.card α at hval
      have h1 := forcingR (mem_linExts.mp hf₁.1) b
      have h2 := forcingR (mem_linExts.mp hf₂.1) b
      exact Fin.ext (by omega)
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter] at hp
    obtain ⟨⟨hg, hgxy⟩, hh⟩ := hp
    refine ⟨combine p.1 p.2, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨mem_linExts.mpr (isLinExt_combine (mem_linExts.mp hg) (mem_linExts.mp hh)), ?_⟩
      refine Fin.lt_def.mpr ?_
      simp only [combine_inl]
      exact Fin.lt_def.mp hgxy
    · refine Prod.ext ?_ ?_
      · funext a; refine Fin.ext ?_; simp only [restrictL_val, combine_inl]
      · funext b; refine Fin.ext ?_; simp only [restrictR_val, combine_inr]; omega

/-- **The before-count of a top-block pair multiplies:**
`e(P ⊕ Q, ↑x < ↑y) = e(P) · e(Q, x<y)` for `x, y ∈ Q`. -/
theorem numBefore_ser_inr (x y : β) :
    numBefore (X := Ser α β) (Sum.inr x) (Sum.inr y)
      = numLinExts (X := α) * numBefore (X := β) x y := by
  classical
  unfold numBefore numLinExts
  rw [← Finset.card_product]
  refine Finset.card_bij
    (fun f hf => (restrictL f (mem_linExts.mp (Finset.mem_filter.mp hf).1),
                  restrictR f (mem_linExts.mp (Finset.mem_filter.mp hf).1))) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hmem, hlt⟩ := hf
    have hL := mem_linExts.mp hmem
    rw [Finset.mem_product, Finset.mem_filter]
    refine ⟨mem_linExts.mpr (isLinExt_restrictL hL),
      ⟨mem_linExts.mpr (isLinExt_restrictR hL), ?_⟩⟩
    refine Fin.lt_def.mpr ?_
    show (f (Sum.inr x)).val - Fintype.card α < (f (Sum.inr y)).val - Fintype.card α
    have h1 := forcingR hL x; have h2 := forcingR hL y
    have hxy := Fin.lt_def.mp hlt
    omega
  · intro f₁ hf₁ f₂ hf₂ heq
    rw [Finset.mem_filter] at hf₁ hf₂
    have hL := congrArg Prod.fst heq
    have hR := congrArg Prod.snd heq
    funext z
    cases z with
    | inl a =>
      have hval := congrArg Fin.val (congrFun hL a)
      simp only [restrictL_val] at hval
      exact Fin.ext hval
    | inr b =>
      have hval := Fin.ext_iff.mp (congrFun hR b)
      change (f₁ (Sum.inr b)).val - Fintype.card α
        = (f₂ (Sum.inr b)).val - Fintype.card α at hval
      have h1 := forcingR (mem_linExts.mp hf₁.1) b
      have h2 := forcingR (mem_linExts.mp hf₂.1) b
      exact Fin.ext (by omega)
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter] at hp
    obtain ⟨hg, ⟨hh, hhxy⟩⟩ := hp
    refine ⟨combine p.1 p.2, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨mem_linExts.mpr (isLinExt_combine (mem_linExts.mp hg) (mem_linExts.mp hh)), ?_⟩
      refine Fin.lt_def.mpr ?_
      simp only [combine_inr]
      have hxy := Fin.lt_def.mp hhxy
      omega
    · refine Prod.ext ?_ ?_
      · funext a; refine Fin.ext ?_; simp only [restrictL_val, combine_inl]
      · funext b; refine Fin.ext ?_; simp only [restrictR_val, combine_inr]; omega

/-- Incomparable bottom-block pairs correspond to incomparable pairs of `P`. -/
theorem incomp_ser_inl (x y : α) :
    Incomp (X := Ser α β) (Sum.inl x) (Sum.inl y) ↔ Incomp (X := α) x y := by
  simp only [Incomp, Ser.inl_le_inl]

/-- Incomparable top-block pairs correspond to incomparable pairs of `Q`. -/
theorem incomp_ser_inr (x y : β) :
    Incomp (X := Ser α β) (Sum.inr x) (Sum.inr y) ↔ Incomp (X := β) x y := by
  simp only [Incomp, Ser.inr_le_inr]

private theorem mul_cancel {a b c : ℕ} (hc : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
  ⟨fun h => Nat.le_of_mul_le_mul_right h hc, fun h => by gcongr⟩

/-- **Adding a block below preserves balance** of a bottom-block pair. -/
theorem isBalancedPair_ser_inl (x y : α) :
    IsBalancedPair (X := Ser α β) (Sum.inl x) (Sum.inl y) ↔ IsBalancedPair (X := α) x y := by
  have hc : 0 < numLinExts (X := β) := numLinExts_pos
  unfold IsBalancedPair
  rw [numBefore_ser_inl, numLinExts_ser, incomp_ser_inl,
    show 3 * (numBefore (X := α) x y * numLinExts (X := β))
      = (3 * numBefore (X := α) x y) * numLinExts (X := β) by ring,
    show 2 * (numLinExts (X := α) * numLinExts (X := β))
      = (2 * numLinExts (X := α)) * numLinExts (X := β) by ring,
    mul_cancel hc, mul_cancel hc]

/-- **Adding a block above preserves balance** of a top-block pair. -/
theorem isBalancedPair_ser_inr (x y : β) :
    IsBalancedPair (X := Ser α β) (Sum.inr x) (Sum.inr y) ↔ IsBalancedPair (X := β) x y := by
  have hc : 0 < numLinExts (X := α) := numLinExts_pos
  unfold IsBalancedPair
  rw [numBefore_ser_inr, numLinExts_ser, incomp_ser_inr,
    show numLinExts (X := α) * numLinExts (X := β)
      = numLinExts (X := β) * numLinExts (X := α) by ring,
    show 3 * (numLinExts (X := α) * numBefore (X := β) x y)
      = (3 * numBefore (X := β) x y) * numLinExts (X := α) by ring,
    show 2 * (numLinExts (X := β) * numLinExts (X := α))
      = (2 * numLinExts (X := β)) * numLinExts (X := α) by ring,
    mul_cancel hc, mul_cancel hc]

/-- **The ordinal-sum reduction.**  If both summands satisfy the conjecture, so
does their ordinal sum: an incomparable pair of `P ⊕ Q` lies wholly in `P` or
wholly in `Q` (there are no cross-incomparabilities), and a balanced pair of that
summand lifts to a balanced pair of `P ⊕ Q`.  Hence it suffices to prove the
conjecture for ordinal-sum-indecomposable posets. -/
theorem oneThirdTwoThirdsFor_ser
    (hα : OneThirdTwoThirdsFor (X := α)) (hβ : OneThirdTwoThirdsFor (X := β)) :
    OneThirdTwoThirdsFor (X := Ser α β) := by
  rintro ⟨u, v, huv⟩
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      obtain ⟨a, b, hab⟩ := hα ⟨x, y, (incomp_ser_inl x y).mp huv⟩
      exact ⟨Sum.inl a, Sum.inl b, (isBalancedPair_ser_inl a b).mpr hab⟩
    | inr y => exact absurd (Ser.inl_le_inr x y) huv.1
  | inr x =>
    cases v with
    | inl y => exact absurd (Ser.inl_le_inr y x) huv.2
    | inr y =>
      obtain ⟨a, b, hab⟩ := hβ ⟨x, y, (incomp_ser_inr x y).mp huv⟩
      exact ⟨Sum.inr a, Sum.inr b, (isBalancedPair_ser_inr a b).mpr hab⟩

end OneThirdTwoThirds
