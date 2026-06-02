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

/-! ### The cross before-count via the position-subset -/

/-- There exists a (the unique) linear extension of any `Fin k`. -/
theorem exists_isLinExt_fin (k : ℕ) : ∃ g : Fin k → Fin (Fintype.card (Fin k)), IsLinExt g := by
  have h := numLinExts_pos (X := Fin k)
  rw [numLinExts, Finset.card_pos] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, mem_linExts.mp hg⟩

/-- **Cross before-count as a subset count.**  The shuffles in which `b_j`
precedes `a₀` correspond, via `F ↦ posSet F`, to the `m`-subsets all of whose
positions exceed `j`. -/
theorem numBefore_inr_inl_eq_card [NeZero m] (j : Fin n) :
    numBefore (X := Fin m ⊕ Fin n) (Sum.inr j) (Sum.inl 0)
      = ((Finset.univ.powersetCard m).filter
          (fun S : Finset (Fin (Fintype.card (Fin m ⊕ Fin n))) => ∀ x ∈ S, (j : ℕ) < x.val)).card := by
  classical
  unfold numBefore
  refine Finset.card_bij (fun F _ => posSet F) ?_ ?_ ?_
  · -- well-defined
    intro F hF
    rw [Finset.mem_filter] at hF
    have hL := mem_linExts.mp hF.1
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, (posSet_card hL.1).trans (Fintype.card_fin m)⟩, ?_⟩
    intro x hx
    have hlt : (j : ℕ) < (F (Sum.inl 0)).val := (cross_lt_iff hL j).mp hF.2
    rw [aMin_eq_min hL] at hlt
    exact lt_of_lt_of_le hlt (Fin.le_def.mp (Finset.min'_le _ _ hx))
  · -- injective
    intro F₁ hF₁ F₂ hF₂ hpos
    simp only at hpos
    rw [Finset.mem_filter] at hF₁ hF₂
    have hL₁ := mem_linExts.mp hF₁.1
    have hL₂ := mem_linExts.mp hF₂.1
    have hLeq : restrictParL F₁ (posSet_card hL₁.1) = restrictParL F₂ (posSet_card hL₂.1) :=
      isLinExt_fin_unique (isLinExt_restrictParL hL₁ _) (isLinExt_restrictParL hL₂ _)
    have hReq : restrictParR F₁ hL₁.1 (compl_posSet_card hL₁.1)
        = restrictParR F₂ hL₂.1 (compl_posSet_card hL₂.1) :=
      isLinExt_fin_unique (isLinExt_restrictParR hL₁ _) (isLinExt_restrictParR hL₂ _)
    funext z
    cases z with
    | inl a =>
      rw [← restrictParL_spec F₁ (posSet_card hL₁.1) a,
        ← restrictParL_spec F₂ (posSet_card hL₂.1) a,
        orderEmbOfFin_congr hpos (posSet_card hL₁.1) (posSet_card hL₂.1), congrFun hLeq a]
    | inr b =>
      have hpc : (posSet F₁)ᶜ = (posSet F₂)ᶜ := by rw [hpos]
      rw [← restrictParR_spec F₁ hL₁.1 (compl_posSet_card hL₁.1) b,
        ← restrictParR_spec F₂ hL₂.1 (compl_posSet_card hL₂.1) b,
        orderEmbOfFin_congr hpc (compl_posSet_card hL₁.1) (compl_posSet_card hL₂.1), congrFun hReq b]
  · -- surjective
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨-, hScard⟩, hcond⟩ := hS
    have hScard' : S.card = Fintype.card (Fin m) := hScard.trans (Fintype.card_fin m).symm
    obtain ⟨ηm, hηm⟩ := exists_isLinExt_fin m
    obtain ⟨ηn, hηn⟩ := exists_isLinExt_fin n
    have hF : IsLinExt (combinePar S hScard' (compl_card_eq hScard') ηm ηn) :=
      isLinExt_combinePar hηm hηn
    have hSne : S.Nonempty := by
      rw [← Finset.card_pos, hScard]; exact Nat.pos_of_ne_zero (NeZero.ne m)
    have hmin0 : combinePar S hScard' (compl_card_eq hScard') ηm ηn (Sum.inl 0) = S.min' hSne := by
      rw [combinePar_inl]
      have hz : ηm 0 = ⟨0, by rw [Fintype.card_fin]; exact Nat.pos_of_ne_zero (NeZero.ne m)⟩ :=
        Fin.ext (isLinExt_fin_val hηm 0)
      rw [hz, Finset.orderEmbOfFin_zero]
    refine ⟨combinePar S hScard' (compl_card_eq hScard') ηm ηn,
      Finset.mem_filter.mpr ⟨mem_linExts.mpr hF, ?_⟩,
      posSet_combinePar (linExt_surjective hηm.1)⟩
    rw [cross_lt_iff hF j, hmin0]
    exact hcond _ (S.min'_mem hSne)

/-- The subset side: `m`-subsets all of whose positions exceed `j` are the
`m`-subsets of an `(m+n-1-j)`-element interval. -/
theorem subsetCount (m n : ℕ) (j : Fin n) :
    ((Finset.univ.powersetCard m).filter
        (fun S : Finset (Fin (Fintype.card (Fin m ⊕ Fin n))) => ∀ x ∈ S, (j : ℕ) < x.val)).card
      = (m + n - 1 - j.val).choose m := by
  have hN : Fintype.card (Fin m ⊕ Fin n) = m + n := by
    rw [card_par, Fintype.card_fin, Fintype.card_fin]
  have hj : j.val < Fintype.card (Fin m ⊕ Fin n) := by rw [hN]; have := j.isLt; omega
  have hfe : (Finset.univ.powersetCard m).filter
        (fun S : Finset (Fin (Fintype.card (Fin m ⊕ Fin n))) => ∀ x ∈ S, (j : ℕ) < x.val)
      = (Finset.Ioi (⟨j.val, hj⟩ : Fin (Fintype.card (Fin m ⊕ Fin n)))).powersetCard m := by
    ext S
    rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hc⟩, hcond⟩
      exact ⟨fun x hx => Finset.mem_Ioi.mpr (Fin.lt_def.mpr (hcond x hx)), hc⟩
    · rintro ⟨hsub, hc⟩
      exact ⟨⟨Finset.subset_univ _, hc⟩, fun x hx => Fin.lt_def.mp (Finset.mem_Ioi.mp (hsub hx))⟩
  rw [hfe, Finset.card_powersetCard, Fin.card_Ioi]
  simp only [hN]

/-- **The cross before-count, closed form:**
`e(Fin m ⊔ Fin n, b_j < a₀) = C(m+n-1-j, m)`. -/
theorem numBefore_inr_inl_finSum [NeZero m] (j : Fin n) :
    numBefore (X := Fin m ⊕ Fin n) (Sum.inr j) (Sum.inl 0) = (m + n - 1 - j.val).choose m := by
  rw [numBefore_inr_inl_eq_card, subsetCount]

/-! ### Binomial arithmetic for the intermediate-value step -/

/-- The exact ratio identity `C(a+b+2,a+1)·(a+1)(b+1) = C(a+b,a)·(a+b+2)(a+b+1)`. -/
theorem choose_ratio_identity (a b : ℕ) :
    (a + b + 2).choose (a + 1) * ((a + 1) * (b + 1))
      = (a + b).choose a * ((a + b + 2) * (a + b + 1)) := by
  have e1 : (a + b + 2).choose (a + 1) * (a + 1).factorial * (b + 1).factorial
      = (a + b + 2).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a + 1 ≤ a + b + 2 by omega)
    rwa [show a + b + 2 - (a + 1) = b + 1 by omega] at h
  have e2 : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rwa [show a + b - a = b by omega] at h
  have h3 : (a + b + 2).factorial = (a + b + 2) * (a + b + 1) * (a + b).factorial := by
    rw [show a + b + 2 = (a + b + 1) + 1 by omega, Nat.factorial_succ,
      show a + b + 1 = (a + b) + 1 by omega, Nat.factorial_succ]; ring
  have key : (a + b + 2).choose (a + 1) * ((a + 1) * (b + 1)) * (a.factorial * b.factorial)
      = (a + b).choose a * ((a + b + 2) * (a + b + 1)) * (a.factorial * b.factorial) := by
    calc (a + b + 2).choose (a + 1) * ((a + 1) * (b + 1)) * (a.factorial * b.factorial)
        = (a + b + 2).choose (a + 1) * (a + 1).factorial * (b + 1).factorial := by
          rw [Nat.factorial_succ a, Nat.factorial_succ b]; ring
      _ = (a + b + 2).factorial := e1
      _ = (a + b + 2) * (a + b + 1) * ((a + b).choose a * a.factorial * b.factorial) := by
          rw [e2, h3]
      _ = (a + b).choose a * ((a + b + 2) * (a + b + 1)) * (a.factorial * b.factorial) := by ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) key

/-- **The intermediate-value step bound, binomial form:**
`3·C(m+n-2,m-1) ≤ C(m+n,m)` for `m,n ≥ 1` — equivalently one `a₀`-row step is at
most `1/3`. -/
theorem three_choose_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h3 : 3 ≤ m + n) :
    3 * (m + n - 2).choose (m - 1) ≤ (m + n).choose m := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- now m = 1 + a, n = 1 + b
  rw [show 1 + a + (1 + b) - 2 = a + b by omega, show 1 + a - 1 = a by omega,
    show 1 + a + (1 + b) = a + b + 2 by omega, show 1 + a = a + 1 by omega]
  -- goal: 3 * C(a+b,a) ≤ C(a+b+2, a+1)
  have hpos : 0 < (a + 1) * (b + 1) := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc 3 * (a + b).choose a * ((a + 1) * (b + 1))
      = (a + b).choose a * (3 * ((a + 1) * (b + 1))) := by ring
    _ ≤ (a + b).choose a * ((a + b + 2) * (a + b + 1)) := by
        apply Nat.mul_le_mul_left
        have hsb := step_bound_arith (m := a + 1) (n := b + 1) (by omega) (by omega) (by omega)
        nlinarith [hsb]
    _ = (a + b + 2).choose (a + 1) * ((a + 1) * (b + 1)) := (choose_ratio_identity a b).symm

/-- The `hstart` binomial bound: `3·C(m+n-1,m-1) ≤ 2·C(m+n,m)` exactly when
`m ≤ 2n` (i.e. `δ(a₀,b₀) = m/(m+n) ≤ 2/3`). -/
theorem three_choose_le_two {m n : ℕ} (hm : 1 ≤ m) (h2 : m ≤ 2 * n) :
    3 * (m + n - 1).choose (m - 1) ≤ 2 * (m + n).choose m := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 1 + a + n - 1 = a + n by omega, show 1 + a - 1 = a by omega,
    show 1 + a + n = a + n + 1 by omega, show 1 + a = a + 1 by omega]
  -- goal: 3 * C(a+n, a) ≤ 2 * C(a+n+1, a+1)
  have hid : (a + n + 1) * (a + n).choose a = (a + n + 1).choose (a + 1) * (a + 1) := by
    have := Nat.add_one_mul_choose_eq (a + n) a
    simpa using this
  have hpos : 0 < a + 1 := by omega
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc 3 * (a + n).choose a * (a + 1)
      = 3 * ((a + n).choose a * (a + 1)) := by ring
    _ ≤ 2 * ((a + n + 1) * (a + n).choose a) := by nlinarith [Nat.choose_pos (show a ≤ a + n by omega)]
    _ = 2 * ((a + n + 1).choose (a + 1) * (a + 1)) := by rw [hid]
    _ = 2 * (a + n + 1).choose (a + 1) * (a + 1) := by ring

/-- `C(m+n,m) ≥ 2` for `m, n ≥ 1` (there are at least two shuffles). -/
theorem two_le_choose_finSum {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : 2 ≤ (m + n).choose m := by
  have h1 : (m + 1).choose m = m + 1 := Nat.choose_succ_self_right m
  have h2 : (m + 1).choose m ≤ (m + n).choose m := Nat.choose_le_choose m (by omega)
  omega

/-- **The cross before-count of `a₀ < b_j`:** `C(m+n,m) − C(m+n-1-j, m)`. -/
theorem numBefore_inl_inr_finSum [NeZero m] (j : Fin n) :
    numBefore (X := Fin m ⊕ Fin n) (Sum.inl 0) (Sum.inr j)
      = (m + n).choose m - (m + n - 1 - j.val).choose m := by
  have hpart := numBefore_add_numBefore (X := Fin m ⊕ Fin n) (Sum.inl 0) (Sum.inr j)
    (Sum.inl_ne_inr)
  rw [numBefore_inr_inl_finSum, numLinExts_finSum] at hpart
  omega

/-! ### The balanced pair: the row case `m ≤ 2n` -/

/-- **Row case.**  When `m ≤ 2n`, the `a₀`-row `j ↦ δ(a₀, b_j)` starts at
`m/(m+n) ≤ 2/3`, climbs to `≈ 1` with steps `≤ 1/3`, so it crosses the balanced
band: `Fin m ⊕ Fin n` has a balanced cross pair. -/
theorem balancedPair_finSum_row [NeZero m] (hn : 1 ≤ n) (h2 : m ≤ 2 * n) :
    ∃ u v : Fin m ⊕ Fin n, IsBalancedPair (X := Fin m ⊕ Fin n) u v := by
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hstep : ∀ k, k < n - 1 →
      3 * ((m + n).choose m - (m + n - 1 - (k + 1)).choose m)
        ≤ 3 * ((m + n).choose m - (m + n - 1 - k).choose m) + (m + n).choose m := by
    intro k hk
    have hA : (m + n - 1 - k).choose m ≤ (m + n).choose m := Nat.choose_le_choose m (by omega)
    have hB : (m + n - 1 - (k + 1)).choose m ≤ (m + n - 1 - k).choose m :=
      Nat.choose_le_choose m (by omega)
    have hpascal : (m + n - 1 - k).choose m
        = (m + n - 2 - k).choose (m - 1) + (m + n - 1 - (k + 1)).choose m := by
      have key := Nat.choose_succ_succ (m + n - 2 - k) (m - 1)
      simp only [Nat.succ_eq_add_one] at key
      rw [show (m + n - 2 - k) + 1 = m + n - 1 - k by omega, show (m - 1) + 1 = m by omega] at key
      rw [show m + n - 1 - (k + 1) = m + n - 2 - k by omega]
      exact key
    have hgap : 3 * (m + n - 2 - k).choose (m - 1) ≤ (m + n).choose m := by
      have hmono : (m + n - 2 - k).choose (m - 1) ≤ (m + n - 2).choose (m - 1) :=
        Nat.choose_le_choose (m - 1) (by omega)
      have h3 : 3 ≤ m + n := by omega
      calc 3 * (m + n - 2 - k).choose (m - 1) ≤ 3 * (m + n - 2).choose (m - 1) := by omega
        _ ≤ (m + n).choose m := three_choose_le hm hn h3
    omega
  have hstart : 3 * ((m + n).choose m - (m + n - 1 - 0).choose m) ≤ 2 * (m + n).choose m := by
    rw [show m + n - 1 - 0 = m + n - 1 by omega]
    have hpascal : (m + n).choose m = (m + n - 1).choose (m - 1) + (m + n - 1).choose m := by
      have key := Nat.choose_succ_succ (m + n - 1) (m - 1)
      simp only [Nat.succ_eq_add_one] at key
      rw [show (m + n - 1) + 1 = m + n by omega, show (m - 1) + 1 = m by omega] at key
      exact key
    have hbound : 3 * (m + n - 1).choose (m - 1) ≤ 2 * (m + n).choose m :=
      three_choose_le_two hm h2
    omega
  have hend : (m + n).choose m ≤ 3 * ((m + n).choose m - (m + n - 1 - (n - 1)).choose m) := by
    rw [show m + n - 1 - (n - 1) = m by omega, Nat.choose_self]
    have := two_le_choose_finSum hm hn
    omega
  obtain ⟨k, hkN, hk1, hk2⟩ := balanced_of_monotone_steps (D := (m + n).choose m) (N := n - 1)
    (fun k => (m + n).choose m - (m + n - 1 - k).choose m) hstep hstart hend
  have hkn : k < n := by omega
  refine ⟨Sum.inl 0, Sum.inr ⟨k, hkn⟩, ?_⟩
  unfold IsBalancedPair
  refine ⟨incomp_inl_inr (0 : Fin m) (⟨k, hkn⟩ : Fin n), ?_, ?_⟩
  · rw [numLinExts_finSum, numBefore_inl_inr_finSum]; exact hk1
  · rw [numLinExts_finSum, numBefore_inl_inr_finSum]; exact hk2

end OneThirdTwoThirds
