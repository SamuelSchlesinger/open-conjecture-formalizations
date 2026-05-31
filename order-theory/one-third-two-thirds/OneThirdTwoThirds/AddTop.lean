import OneThirdTwoThirds.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.WithTopBot

/-!
# The 1/3–2/3 conjecture — adding a global maximum

Adjoining a top element `⊤` above all of `P` (the poset `WithTop P`, i.e. the
ordinal sum `P ⊕ •`) does not change any balance: `⊤` is forced to the last
position of every linear extension, so the linear extensions of `WithTop P` are
in bijection with those of `P`, and the relative order of two old elements is
untouched.  Hence

```
e(WithTop P)        = e(P)            (numLinExts_withTop)
e(WithTop P, x<y)   = e(P, x<y)       (numBefore_withTop)
```

so `δ` is preserved and the conjecture for `WithTop P` reduces to `P`
(`oneThirdTwoThirdsFor_withTop`).  Dually (via `Duality`) one may also strip a
global *minimum*.

This is the ordinal-sum reduction in the special case of a one-point top
summand; the forcing argument (`⊤` lands on the top `Fin`-position) is the crux.
`sorry`-free.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableLE α]

omit [DecidableEq α] [PartialOrder α] [DecidableLE α] in
theorem card_withTop : Fintype.card (WithTop α) = Fintype.card α + 1 := Fintype.card_option

omit [DecidableEq α] [DecidableLE α] in
/-- In any linear extension of `WithTop α`, the top `⊤` occupies the last
position `|α|`. -/
theorem topval {f : WithTop α → Fin (Fintype.card (WithTop α))} (hf : IsLinExt f) :
    (f ⊤).val = Fintype.card α := by
  obtain ⟨hinj, hmono⟩ := hf
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [Fintype.card_fin]⟩
  have hmax : ∀ x : Fin (Fintype.card (WithTop α)), x ≤ f ⊤ := by
    intro x
    obtain ⟨z, rfl⟩ := hbij.surjective x
    exact hmono z ⊤ le_top
  have h1 : Fintype.card (WithTop α) - 1 ≤ (f ⊤).val := by
    have h := hmax ⟨Fintype.card (WithTop α) - 1, by have := card_withTop (α := α); omega⟩
    simpa [Fin.le_def] using h
  have h2 := (f ⊤).isLt
  have := card_withTop (α := α)
  omega

omit [DecidableEq α] [DecidableLE α] in
/-- **Forcing**: every coerced element `↑a` gets a position `< |α|`. -/
theorem forcing {f : WithTop α → Fin (Fintype.card (WithTop α))} (hf : IsLinExt f) (a : α) :
    (f ↑a).val < Fintype.card α := by
  have htv := topval hf
  have hne : (f (↑a)).val ≠ (f ⊤).val := fun h => WithTop.coe_ne_top (hf.1 (Fin.ext h))
  have h2 := (f (↑a)).isLt
  have := card_withTop (α := α)
  rw [htv] at hne
  omega

/-- Reconstruct a `WithTop α`-ranking from an `α`-ranking by sending `⊤` to the
top position. -/
def extendTop (g : α → Fin (Fintype.card α)) : WithTop α → Fin (Fintype.card (WithTop α)) :=
  fun z => WithTop.recTopCoe ⟨Fintype.card α, by rw [card_withTop]; omega⟩
    (fun a => ⟨(g a).val, by rw [card_withTop]; have := (g a).isLt; omega⟩) z

omit [DecidableEq α] [PartialOrder α] [DecidableLE α] in
@[simp] theorem extendTop_top (g : α → Fin (Fintype.card α)) :
    (extendTop g ⊤).val = Fintype.card α := rfl

omit [DecidableEq α] [PartialOrder α] [DecidableLE α] in
@[simp] theorem extendTop_coe (g : α → Fin (Fintype.card α)) (a : α) :
    (extendTop g ↑a).val = (g a).val := rfl

omit [DecidableEq α] [DecidableLE α] in
theorem isLinExt_extendTop {g : α → Fin (Fintype.card α)} (hg : IsLinExt g) :
    IsLinExt (extendTop g) := by
  obtain ⟨hinj, hmono⟩ := hg
  refine ⟨?_, ?_⟩
  · -- injective
    intro z w hzw
    induction z using WithTop.recTopCoe with
    | top =>
      induction w using WithTop.recTopCoe with
      | top => rfl
      | coe b =>
        exfalso
        have h := congrArg Fin.val hzw
        rw [extendTop_top, extendTop_coe] at h
        have := (g b).isLt; omega
    | coe a =>
      induction w using WithTop.recTopCoe with
      | top =>
        exfalso
        have h := congrArg Fin.val hzw
        rw [extendTop_coe, extendTop_top] at h
        have := (g a).isLt; omega
      | coe b =>
        have h := congrArg Fin.val hzw
        rw [extendTop_coe, extendTop_coe] at h
        rw [WithTop.coe_eq_coe]
        exact hinj (Fin.ext h)
  · -- monotone
    intro z w hzw
    induction z using WithTop.recTopCoe with
    | top =>
      -- ⊤ ≤ w forces w = ⊤
      rw [top_le_iff] at hzw; subst hzw; exact le_refl _
    | coe a =>
      induction w using WithTop.recTopCoe with
      | top =>
        rw [Fin.le_def, extendTop_coe, extendTop_top]
        have := (g a).isLt; omega
      | coe b =>
        rw [Fin.le_def, extendTop_coe, extendTop_coe]
        have : g a ≤ g b := hmono a b (WithTop.coe_le_coe.mp hzw)
        rwa [Fin.le_def] at this

/-- **Linear extensions are unchanged by adding a top:** `e(WithTop P) = e(P)`. -/
theorem numLinExts_withTop : numLinExts (X := WithTop α) = numLinExts (X := α) := by
  classical
  unfold numLinExts
  refine Finset.card_bij
    (fun f hf a => (⟨(f ↑a).val, forcing (mem_linExts.mp hf) a⟩ : Fin (Fintype.card α)))
    ?_ ?_ ?_
  · -- the restriction is a linear extension of `α`
    intro f hf
    rw [mem_linExts] at hf ⊢
    obtain ⟨hinj, hmono⟩ := hf
    refine ⟨?_, ?_⟩
    · intro a b hab
      simp only [Fin.mk.injEq] at hab
      exact WithTop.coe_injective (hinj (Fin.ext hab))
    · intro a b hab
      simp only [Fin.mk_le_mk]
      exact Fin.le_def.mp (hmono _ _ (WithTop.coe_le_coe.mpr hab))
  · -- injective
    intro f₁ hf₁ f₂ hf₂ heq
    rw [mem_linExts] at hf₁ hf₂
    funext z
    induction z using WithTop.recTopCoe with
    | top => exact Fin.ext (by rw [topval hf₁, topval hf₂])
    | coe a =>
      have h := congrFun heq a
      simp only [Fin.mk.injEq] at h
      exact Fin.ext h
  · -- surjective
    intro g hg
    refine ⟨extendTop g, ?_, ?_⟩
    · rw [mem_linExts]; exact isLinExt_extendTop (mem_linExts.mp hg)
    · funext a; exact Fin.ext (extendTop_coe g a)

/-- **The before-count is unchanged by adding a top:** `e(WithTop P, ↑x<↑y) =
e(P, x<y)`.  The relative order of two old elements is untouched. -/
theorem numBefore_withTop (x y : α) :
    numBefore (X := WithTop α) (↑x) (↑y) = numBefore (X := α) x y := by
  classical
  unfold numBefore linExts
  refine Finset.card_bij
    (fun f hf a => (⟨(f ↑a).val,
      forcing (mem_linExts.mp (Finset.mem_filter.mp hf).1) a⟩ : Fin (Fintype.card α)))
    ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    obtain ⟨hmem, hlt⟩ := hf
    obtain ⟨hinj, hmono⟩ := mem_linExts.mp hmem
    refine ⟨mem_linExts.mpr ⟨?_, ?_⟩, ?_⟩
    · intro a b hab
      simp only [Fin.mk.injEq] at hab
      exact WithTop.coe_injective (hinj (Fin.ext hab))
    · intro a b hab
      simp only [Fin.mk_le_mk]
      exact Fin.le_def.mp (hmono _ _ (WithTop.coe_le_coe.mpr hab))
    · simp only [Fin.mk_lt_mk]; exact Fin.lt_def.mp hlt
  · intro f₁ hf₁ f₂ hf₂ heq
    rw [Finset.mem_filter] at hf₁ hf₂
    have h1 := mem_linExts.mp hf₁.1
    have h2 := mem_linExts.mp hf₂.1
    funext z
    induction z using WithTop.recTopCoe with
    | top => exact Fin.ext (by rw [topval h1, topval h2])
    | coe a => have h := congrFun heq a; simp only [Fin.mk.injEq] at h; exact Fin.ext h
  · intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hmemg, hltg⟩ := hg
    refine ⟨extendTop g, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨mem_linExts.mpr (isLinExt_extendTop (mem_linExts.mp hmemg)), ?_⟩
      exact Fin.lt_def.mpr (Fin.lt_def.mp hltg)
    · funext a; exact Fin.ext (extendTop_coe g a)

omit [Fintype α] [DecidableEq α] [DecidableLE α] in
/-- Incomparability of `↑x, ↑y` in `WithTop α` is the same as that of `x, y`. -/
theorem incomp_coe (x y : α) :
    Incomp (X := WithTop α) (↑x) (↑y) ↔ Incomp (X := α) x y := by
  simp only [Incomp, WithTop.coe_le_coe]

/-- **Adding a top preserves balanced pairs.** -/
theorem isBalancedPair_withTop (x y : α) :
    IsBalancedPair (X := WithTop α) (↑x) (↑y) ↔ IsBalancedPair (X := α) x y := by
  unfold IsBalancedPair
  rw [numBefore_withTop, numLinExts_withTop, incomp_coe]

/-- **The conjecture for `WithTop P` reduces to `P`.**  Adjoining a global
maximum cannot create or destroy a balanced pair (the top is comparable to
everything, and old pairs keep their balance). -/
theorem oneThirdTwoThirdsFor_withTop (h : OneThirdTwoThirdsFor (X := α)) :
    OneThirdTwoThirdsFor (X := WithTop α) := by
  rintro ⟨u, v, huv⟩
  have hu : u ≠ ⊤ := fun htop => huv.2 (by rw [htop]; exact le_top)
  have hv : v ≠ ⊤ := fun htop => huv.1 (by rw [htop]; exact le_top)
  obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.mp hu
  obtain ⟨y, rfl⟩ := WithTop.ne_top_iff_exists.mp hv
  obtain ⟨a, b, hab⟩ := h ⟨x, y, (incomp_coe x y).mp huv⟩
  exact ⟨↑a, ↑b, (isBalancedPair_withTop a b).mpr hab⟩

end OneThirdTwoThirds
