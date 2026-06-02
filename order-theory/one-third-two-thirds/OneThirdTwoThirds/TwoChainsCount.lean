import OneThirdTwoThirds.TwoChains
import Mathlib.Order.Hom.Set
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

end OneThirdTwoThirds
