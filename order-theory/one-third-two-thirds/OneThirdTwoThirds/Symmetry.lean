import OneThirdTwoThirds.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# The 1/3–2/3 conjecture — the symmetric (twin) case

The computational exploration found that highly symmetric posets — antichains and
ordinal sums of antichains — always realize the *perfect* balance `δ = 1/2`
(`research/exploration.md`).  This file explains that analytically and turns it
into a class result for the conjecture.

The mechanism: if an **order-automorphism** `σ` of `P` swaps `x` and `y`, then
precomposition `f ↦ f ∘ σ` is a bijection of the linear extensions that
exchanges "`x` before `y`" with "`y` before `x`".  Hence
`e(P, x<y) = e(P, y<x)`, so `δ(x,y) = 1/2` and the pair is balanced
(`isBalancedPair_of_orderIso_swap`).

The natural source of such an automorphism is a pair of **twins** (interchangeable
elements): incomparable `x, y` with the same strict relations to every other
element.  Swapping twins is an automorphism, so a poset with an incomparable
twin pair satisfies the conjecture outright (`oneThirdTwoThirdsFor_of_twin`).
This is the order-theoretic analogue of the twin-deletion reduction in the
Frankl campaign.

Everything here is `sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {X : Type*} [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]

omit [DecidableEq X] [DecidableLE X] in
/-- Precomposition with an order-automorphism preserves being a linear
extension. -/
theorem isLinExt_comp_orderIso (σ : X ≃o X) {f : X → Fin (Fintype.card X)}
    (hf : IsLinExt f) : IsLinExt (fun a => f (σ a)) := by
  obtain ⟨hinj, hmono⟩ := hf
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact σ.injective (hinj hab)
  · intro a b hab
    exact hmono _ _ (σ.monotone hab)

/-- **Swapping by an automorphism flips the before-count.**  If an
order-automorphism `σ` swaps `x` and `y`, then `e(P, x<y) = e(P, y<x)`.

Proof: `f ↦ f ∘ σ` is a bijection of linear extensions; since `σ x = y` and
`σ y = x`, it sends an extension with `x` before `y` to one with `y` before
`x`. -/
theorem numBefore_swap (σ : X ≃o X) {x y : X} (hx : σ x = y) (hy : σ y = x) :
    numBefore x y = numBefore y x := by
  unfold numBefore linExts
  refine Finset.card_bij (fun f _ => fun a => f (σ a)) ?_ ?_ ?_
  · -- maps `{x before y}` into `{y before x}`
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    obtain ⟨hmem, hlt⟩ := hf
    rw [Finset.mem_filter] at hmem
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, isLinExt_comp_orderIso σ hmem.2⟩, ?_⟩
    -- goal: (f ∘ σ) y < (f ∘ σ) x; i.e. f (σ y) < f (σ x); i.e. f x < f y
    simp only [hx, hy]
    exact hlt
  · -- injective
    intro f₁ _ f₂ _ heq
    funext c
    have := congrFun heq (σ.symm c)
    simpa only [OrderIso.apply_symm_apply] using this
  · -- surjective
    intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hmem, hlt⟩ := hg
    rw [Finset.mem_filter] at hmem
    refine ⟨fun a => g (σ.symm a), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact isLinExt_comp_orderIso σ.symm hmem.2
      · -- goal: (g ∘ σ.symm) x < (g ∘ σ.symm) y; i.e. g (σ.symm x) < g (σ.symm y)
        -- σ.symm x = y, σ.symm y = x (from hx, hy)
        have hsx : σ.symm x = y := by rw [← hy, OrderIso.symm_apply_apply]
        have hsy : σ.symm y = x := by rw [← hx, OrderIso.symm_apply_apply]
        show g (σ.symm x) < g (σ.symm y)
        rw [hsx, hsy]; exact hlt
    · -- (g ∘ σ.symm) ∘ σ = g
      funext a; simp only [OrderIso.symm_apply_apply]

/-- **An automorphism-swapped incomparable pair is balanced** (`δ = 1/2`).  If
an order-automorphism swaps the incomparable pair `{x, y}`, then `{x, y}` is a
balanced pair. -/
theorem isBalancedPair_of_orderIso_swap (σ : X ≃o X) {x y : X}
    (hx : σ x = y) (hy : σ y = x) (hinc : Incomp x y) : IsBalancedPair x y := by
  have hswap := numBefore_swap σ hx hy
  have hpart := numBefore_add_numBefore x y hinc.ne
  -- 2 * numBefore x y = numLinExts
  have h2 : 2 * numBefore x y = numLinExts (X := X) := by omega
  refine ⟨hinc, ?_, ?_⟩ <;> omega

/-! ### Twins -/

/-- `x` and `y` are **twins** (interchangeable) when they are incomparable and
have exactly the same strict order-relations to every *other* element. -/
def IsTwin (x y : X) : Prop :=
  Incomp x y ∧ ∀ z : X, z ≠ x → z ≠ y → (x ≤ z ↔ y ≤ z) ∧ (z ≤ x ↔ z ≤ y)

omit [Fintype X] [DecidableLE X] in
/-- Swapping a pair of twins is monotone (the key step in building the
automorphism).  The two cases that would break monotonicity — `x ≤ y` or
`y ≤ x` — are excluded by incomparability; every other case uses the twin
property. -/
theorem twinSwap_monotone {x y : X} (h : IsTwin x y) :
    ∀ a b : X, a ≤ b → Equiv.swap x y a ≤ Equiv.swap x y b := by
  obtain ⟨hinc, htw⟩ := h
  intro a b hab
  by_cases hax : a = x
  · subst hax
    rw [Equiv.swap_apply_left]
    by_cases hbx : b = a
    · subst hbx; simp
    · by_cases hby : b = y
      · subst hby; exact absurd hab hinc.1
      · rw [Equiv.swap_apply_of_ne_of_ne hbx hby]
        exact ((htw b hbx hby).1).mp hab
  · by_cases hay : a = y
    · subst hay
      rw [Equiv.swap_apply_right]
      by_cases hbx : b = x
      · subst hbx; exact absurd hab hinc.2
      · by_cases hby : b = a
        · subst hby; simp
        · rw [Equiv.swap_apply_of_ne_of_ne hbx hby]
          exact ((htw b hbx hby).1).mpr hab
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]
      by_cases hbx : b = x
      · subst hbx; rw [Equiv.swap_apply_left]
        exact ((htw a hax hay).2).mp hab
      · by_cases hby : b = y
        · subst hby; rw [Equiv.swap_apply_right]
          exact ((htw a hax hay).2).mpr hab
        · rw [Equiv.swap_apply_of_ne_of_ne hbx hby]; exact hab

/-- Swapping a pair of twins is an order-automorphism of the poset. -/
def twinSwap {x y : X} (h : IsTwin x y) : X ≃o X where
  toEquiv := Equiv.swap x y
  map_rel_iff' := by
    intro a b
    refine ⟨fun hle => ?_, twinSwap_monotone h a b⟩
    have := twinSwap_monotone h _ _ hle
    simpa only [Equiv.swap_apply_self] using this

omit [Fintype X] [DecidableLE X] in
@[simp] theorem twinSwap_apply {x y : X} (h : IsTwin x y) (a : X) :
    twinSwap h a = Equiv.swap x y a := rfl

/-- **The conjecture holds for any poset with an incomparable twin pair**: the
twin pair is balanced with `δ = 1/2`. -/
theorem isBalancedPair_of_twin {x y : X} (h : IsTwin x y) : IsBalancedPair x y := by
  have hx : twinSwap h x = y := by rw [twinSwap_apply]; exact Equiv.swap_apply_left x y
  have hy : twinSwap h y = x := by rw [twinSwap_apply]; exact Equiv.swap_apply_right x y
  exact isBalancedPair_of_orderIso_swap (twinSwap h) hx hy h.1

/-- If a poset has a pair of twins, it satisfies the conjecture. -/
theorem oneThirdTwoThirdsFor_of_twin {x y : X} (h : IsTwin x y) :
    OneThirdTwoThirdsFor (X := X) :=
  fun _ => ⟨x, y, isBalancedPair_of_twin h⟩

/-! ### Antichains

In a poset with the *discrete* order (`a ≤ b ↔ a = b` — i.e. an antichain),
every two distinct elements are twins: neither relates to anything, so the twin
condition holds vacuously.  Hence every incomparable pair is balanced with
`δ = 1/2`, matching the exploration's finding that antichains realize perfect
balance. -/

omit [Fintype X] [DecidableEq X] [DecidableLE X] in
/-- In a discretely-ordered poset (an antichain), any two distinct elements are
twins. -/
theorem isTwin_of_discrete (hdisc : ∀ a b : X, a ≤ b → a = b) {x y : X}
    (hxy : x ≠ y) : IsTwin x y := by
  refine ⟨⟨fun h => hxy (hdisc x y h), fun h => hxy (hdisc y x h).symm⟩, ?_⟩
  intro z hzx hzy
  refine ⟨⟨fun h => absurd (hdisc x z h) ?_, fun h => absurd (hdisc y z h) ?_⟩,
          ⟨fun h => absurd (hdisc z x h) ?_, fun h => absurd (hdisc z y h) ?_⟩⟩
  · exact fun heq => hzx heq.symm
  · exact fun heq => hzy heq.symm
  · exact hzx
  · exact hzy

/-- **An antichain (discrete order) satisfies the conjecture** — with every
incomparable pair perfectly balanced (`δ = 1/2`). -/
theorem oneThirdTwoThirdsFor_of_discrete (hdisc : ∀ a b : X, a ≤ b → a = b) :
    OneThirdTwoThirdsFor (X := X) :=
  fun ⟨x, y, hxy⟩ => ⟨x, y, isBalancedPair_of_twin (isTwin_of_discrete hdisc hxy.ne)⟩

end OneThirdTwoThirds
