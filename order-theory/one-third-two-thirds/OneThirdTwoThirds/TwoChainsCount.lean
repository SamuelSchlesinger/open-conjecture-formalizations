import OneThirdTwoThirds.TwoChains
import Mathlib.Order.Hom.Set
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Choose.Basic

/-!
# The 1/3–2/3 conjecture — counting for the two-chains kernel

This file builds the *counting* input that `TwoChains` left open for a disjoint
union of two chains, modelled concretely as `Fin m ⊕ Fin n`.

Proved here (`sorry`-free):

* a chain has a **unique** linear extension (`isLinExt_fin_unique`,
  `numLinExts_fin`);
* hence the two-chains shuffle count `e(Fin m ⊕ Fin n) = C(m+n, m)`
  (`numLinExts_finSum`).

The remaining counting lemma — the crux — is the **position distribution of the
chain minimum `a₀`**: `#{F : F(↑0) = k} = C(m+n−1−k, m−1)`.  Because `a₀` is the
bottom of the `α`-chain, in *every* linear extension it is preceded only by a
prefix of `β`, so its position **equals** its `β`-rank; counting the shuffles of
the `m−1` remaining `a`'s with the `n−k` remaining `b`'s gives the binomial.
From it the cross before-count `e(Fin m ⊕ Fin n, ↑0 < ↑j) = C(m+n,m) − C(m+n−1−j, m)`
and the three inputs (`hstart`, `hend`, `hstep` via `step_bound_arith`) of
`balanced_of_monotone_steps` follow, yielding the balanced cross pair.  That
distribution count, the IVT assembly, and the transfer to abstract chains (to
discharge `oneThirdTwoThirdsFor_par`'s `hcross`) are the next steps.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

open Finset

/-! ### Order-enumeration value bounds in `Fin N` -/

/-- The `j`-th smallest element of a finset of `Fin N` has value at least `j`. -/
theorem orderEmbOfFin_val_ge {N k : ℕ} (s : Finset (Fin N)) (h : s.card = k) (j : Fin k) :
    (j : ℕ) ≤ (s.orderEmbOfFin h j).val := by
  have key : ∀ i : ℕ, (hi : i < k) → i ≤ (s.orderEmbOfFin h ⟨i, hi⟩).val := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ p ih =>
      intro hp
      have hp' : p < k := Nat.lt_of_succ_lt hp
      have hlt : (s.orderEmbOfFin h ⟨p, hp'⟩).val < (s.orderEmbOfFin h ⟨p + 1, hp⟩).val :=
        (s.orderEmbOfFin h).strictMono (by simp [Fin.lt_def])
      have := ih hp'
      omega
  simpa using key j.val j.isLt

/-! ### A chain has a unique linear extension -/

/-- Any two linear extensions of `Fin k` coincide: a monotone injection
`Fin k → Fin (card)` is the unique order isomorphism. -/
theorem isLinExt_fin_unique {k : ℕ} {f g : Fin k → Fin (Fintype.card (Fin k))}
    (hf : IsLinExt f) (hg : IsLinExt g) : f = g := by
  have hfmono : Monotone f := fun a b h => hf.2 a b h
  have hgmono : Monotone g := fun a b h => hg.2 a b h
  have hfsm : StrictMono f := Monotone.strictMono_of_injective hfmono hf.1
  have hgsm : StrictMono g := Monotone.strictMono_of_injective hgmono hg.1
  have hfs : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf.1, by simp⟩).surjective
  have hgs : Function.Surjective g :=
    ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg.1, by simp⟩).surjective
  have hsub := Subsingleton.elim (StrictMono.orderIsoOfSurjective f hfsm hfs)
    (StrictMono.orderIsoOfSurjective g hgsm hgs)
  funext x
  have := congrArg (fun e : Fin k ≃o Fin (Fintype.card (Fin k)) => e x) hsub
  simpa [StrictMono.orderIsoOfSurjective] using this

/-- The unique linear extension of `Fin k` is the identity (up to the `card`
coercion): it sends `j` to position `j`. -/
theorem isLinExt_fin_val {k : ℕ} {η : Fin k → Fin (Fintype.card (Fin k))}
    (hη : IsLinExt η) (j : Fin k) : (η j).val = j.val := by
  have hsm : StrictMono η :=
    Monotone.strictMono_of_injective (fun a b h => hη.2 a b h) hη.1
  have hsurj : Function.Surjective η :=
    ((Fintype.bijective_iff_injective_and_card η).mpr ⟨hη.1, by simp⟩).surjective
  have hsub := Subsingleton.elim (StrictMono.orderIsoOfSurjective η hsm hsurj)
    (Fin.castOrderIso (Fintype.card_fin k).symm)
  have := congrArg (fun e : Fin k ≃o Fin (Fintype.card (Fin k)) => (e j).val) hsub
  simpa [StrictMono.orderIsoOfSurjective] using this

/-- A chain `Fin k` has exactly one linear extension. -/
theorem numLinExts_fin (k : ℕ) : numLinExts (X := Fin k) = 1 := by
  have hpos : 1 ≤ numLinExts (X := Fin k) := numLinExts_pos
  have hle : numLinExts (X := Fin k) ≤ 1 := by
    rw [numLinExts]
    refine Finset.card_le_one.mpr (fun f hf g hg => ?_)
    exact isLinExt_fin_unique (mem_linExts.mp hf) (mem_linExts.mp hg)
  omega

/-- **Two chains shuffle:** `e(Fin m ⊔ Fin n) = C(m+n, m)`. -/
theorem numLinExts_finSum (m n : ℕ) :
    numLinExts (X := Fin m ⊕ Fin n) = (m + n).choose m := by
  rw [numLinExts_par_eq_choose, numLinExts_fin, numLinExts_fin, Fintype.card_fin, Fintype.card_fin]
  ring

/-! ### The position of the chain minimum equals its `β`-rank -/

variable {m n : ℕ}

/-- In a linear extension of `Fin m ⊕ Fin n`, everything below the minimum `↑0` of
the first chain is a second-chain element; so the number of `b`'s before `↑0`
equals the **position** of `↑0`. -/
theorem card_inr_before_aMin [NeZero m]
    {F : (Fin m ⊕ Fin n) → Fin (Fintype.card (Fin m ⊕ Fin n))} (hF : IsLinExt F) :
    (Finset.univ.filter (fun b : Fin n => F (Sum.inr b) < F (Sum.inl 0))).card
      = (F (Sum.inl 0)).val := by
  classical
  have hbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hF.1, (Fintype.card_fin _).symm⟩
  have hcard : (F (Sum.inl 0)).val = (Finset.Iio (F (Sum.inl 0))).card := (Fin.card_Iio _).symm
  rw [hcard]
  refine Finset.card_bij (fun b _ => F (Sum.inr b)) ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact Finset.mem_Iio.mpr hb.2
  · intro b₁ _ b₂ _ heq
    exact Sum.inr_injective (hF.1 heq)
  · intro p hp
    rw [Finset.mem_Iio] at hp
    obtain ⟨z, rfl⟩ := hbij.surjective p
    cases z with
    | inl a =>
      have h1 : F (Sum.inl 0) ≤ F (Sum.inl a) :=
        hF.2 _ _ ((par_inl_le_inl 0 a).mpr (Fin.le_def.mpr (Nat.zero_le _)))
      exact absurd h1 (not_le.mpr hp)
    | inr b =>
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩

/-- The position of the `j`-th `b` is at least `j` (it is the `j`-th smallest of
its block). -/
theorem aux_inr_val_ge [NeZero m]
    {F : (Fin m ⊕ Fin n) → Fin (Fintype.card (Fin m ⊕ Fin n))} (hF : IsLinExt F) (b : Fin n) :
    (b : ℕ) ≤ (F (Sum.inr b)).val := by
  have hc : (posSet F)ᶜ.card = Fintype.card (Fin n) := compl_posSet_card hF.1
  have hspec := restrictParR_spec F hF.1 hc b
  have h1 : (restrictParR F hF.1 hc b).val ≤ (F (Sum.inr b)).val := by
    rw [← hspec]; exact orderEmbOfFin_val_ge (posSet F)ᶜ hc (restrictParR F hF.1 hc b)
  have h2 : (restrictParR F hF.1 hc b).val = b.val :=
    isLinExt_fin_val (isLinExt_restrictParR hF hc) b
  omega

/-- **Cross comparison ↔ rank comparison:** `b_j` precedes `a₀` iff `j` is below
`a₀`'s position.  (The `b`'s before `a₀` are exactly the first `(F ↑0)`-many.) -/
theorem cross_lt_iff [NeZero m]
    {F : (Fin m ⊕ Fin n) → Fin (Fintype.card (Fin m ⊕ Fin n))} (hF : IsLinExt F) (j : Fin n) :
    F (Sum.inr j) < F (Sum.inl 0) ↔ (j : ℕ) < (F (Sum.inl 0)).val := by
  classical
  set t := (F (Sum.inl 0)).val with ht
  have hcard1 : (Finset.univ.filter (fun b : Fin n => F (Sum.inr b) < F (Sum.inl 0))).card = t :=
    card_inr_before_aMin hF
  have hsub : (Finset.univ.filter (fun b : Fin n => F (Sum.inr b) < F (Sum.inl 0)))
      ⊆ Finset.univ.filter (fun b : Fin n => (b : ℕ) < t) := by
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hlt : (F (Sum.inr b)).val < t := Fin.lt_def.mp hb.2
    have hge : (b : ℕ) ≤ (F (Sum.inr b)).val := aux_inr_val_ge hF b
    omega
  have himg : (Finset.univ.filter (fun b : Fin n => (b : ℕ) < t)).image (fun b => b.val)
      ⊆ Finset.range t := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hb).2
  have hcard2 : (Finset.univ.filter (fun b : Fin n => (b : ℕ) < t)).card ≤ t :=
    calc (Finset.univ.filter (fun b : Fin n => (b : ℕ) < t)).card
        = ((Finset.univ.filter (fun b : Fin n => (b : ℕ) < t)).image (fun b => b.val)).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.range t).card := Finset.card_le_card himg
      _ = t := Finset.card_range t
  have heq : (Finset.univ.filter (fun b : Fin n => F (Sum.inr b) < F (Sum.inl 0)))
      = Finset.univ.filter (fun b : Fin n => (b : ℕ) < t) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard1]; exact hcard2)
  constructor
  · intro h
    have hmem : j ∈ Finset.univ.filter (fun b : Fin n => F (Sum.inr b) < F (Sum.inl 0)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [heq, Finset.mem_filter] at hmem
    exact hmem.2
  · intro h
    have hmem : j ∈ Finset.univ.filter (fun b : Fin n => (b : ℕ) < t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← heq, Finset.mem_filter] at hmem
    exact hmem.2

/-- `a₀ = ↑0` lands on the minimum of its position-set (it is below every other
`a`). -/
theorem aMin_eq_min [NeZero m]
    {F : (Fin m ⊕ Fin n) → Fin (Fintype.card (Fin m ⊕ Fin n))} (hF : IsLinExt F) :
    F (Sum.inl 0) = (posSet F).min' ⟨F (Sum.inl 0), mem_posSet F 0⟩ := by
  refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (mem_posSet F 0))
  intro x hx
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
  exact hF.2 _ _ ((par_inl_le_inl 0 a).mpr (Fin.le_def.mpr (Nat.zero_le _)))

end OneThirdTwoThirds
