import OneThirdTwoThirds.Defs
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Sort

/-!
# The 1/3–2/3 conjecture — counting infrastructure

This file proves the foundational facts about the linear-extension count that
the rest of the project relies on:

* `numBefore_add_numBefore` — the **partition identity**
  `e(P, x<y) + e(P, y<x) = e(P)` for any two distinct elements.  Every linear
  extension assigns distinct positions to `x ≠ y`, so it places `x` before `y`
  or `y` before `x`, exclusively.
* `numLinExts_pos` — `e(P) > 0`: every finite poset has at least one linear
  extension (the finite, computational form of Szpilrajn's theorem, obtained
  by composing `Mathlib`'s `toLinearExtension` with `monoEquivOfFin`).
* `isBalancedPair_comm` — being a balanced pair is symmetric in `x, y`.
* `oneThirdTwoThirdsFor_of_total` — a chain (totally ordered poset) satisfies
  the conjecture vacuously, as it has no incomparable pair.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {X : Type*} [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]

/-- Membership in `linExts` unpacks to the `IsLinExt` predicate. -/
theorem mem_linExts {f : X → Fin (Fintype.card X)} :
    f ∈ linExts (X := X) ↔ IsLinExt f := by
  unfold linExts
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ f, h⟩⟩

/-- A linear extension assigns distinct positions to distinct elements. -/
theorem linExt_apply_ne {f : X → Fin (Fintype.card X)} (hf : f ∈ linExts (X := X))
    {x y : X} (hxy : x ≠ y) : f x ≠ f y := by
  intro h
  exact hxy ((mem_linExts.mp hf).1 h)

/-- **Partition identity.**  For any two distinct elements `x ≠ y`,
`e(P, x<y) + e(P, y<x) = e(P)`: each linear extension places `x` before `y`
or `y` before `x`, and these are mutually exclusive and exhaustive. -/
theorem numBefore_add_numBefore (x y : X) (hxy : x ≠ y) :
    numBefore x y + numBefore y x = numLinExts (X := X) := by
  unfold numBefore numLinExts
  rw [← Finset.card_filter_add_card_filter_not (s := linExts (X := X))
        (p := fun f => f x < f y)]
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro f hf
  have hne : f x ≠ f y := linExt_apply_ne hf hxy
  constructor
  · intro h; exact not_lt.mpr (le_of_lt h)
  · intro h
    rcases lt_or_gt_of_ne (Ne.symm hne) with h' | h'
    · exact h'
    · exact absurd h' h

/-- `e(P) > 0`: every finite poset has at least one linear extension.

We build an explicit linear extension by composing `Mathlib`'s
`toLinearExtension : X →o LinearExtension X` (Szpilrajn: the partial order
extends to a linear order on the same carrier) with the monotone bijection
`monoEquivOfFin` of that finite linear order onto `Fin |X|`.  The composite is
injective (both factors are) and monotone for the original order (both factors
are monotone), hence a member of `linExts`. -/
theorem numLinExts_pos : 0 < numLinExts (X := X) := by
  classical
  letI : Fintype (LinearExtension X) := (inferInstanceAs (Fintype X))
  have hcard : Fintype.card (LinearExtension X) = Fintype.card X := rfl
  let e₂ : LinearExtension X ≃o Fin (Fintype.card X) :=
    (monoEquivOfFin (LinearExtension X) hcard).symm
  let f : X → Fin (Fintype.card X) := fun x => e₂ (toLinearExtension x)
  have hf : IsLinExt f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have h := e₂.injective hab
      exact h
    · intro a b hab
      exact e₂.monotone (toLinearExtension.monotone hab)
  unfold numLinExts linExts
  rw [Finset.card_pos]
  exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf⟩⟩

/-- `e(P, x<y) ≤ e(P)`. -/
theorem numBefore_le_numLinExts (x y : X) (hxy : x ≠ y) :
    numBefore x y ≤ numLinExts (X := X) := by
  rw [← numBefore_add_numBefore x y hxy]; exact Nat.le_add_right _ _

omit [Fintype X] [DecidableEq X] [DecidableLE X] in
/-- Incomparability is symmetric. -/
theorem Incomp.symm {x y : X} (h : Incomp x y) : Incomp y x := ⟨h.2, h.1⟩

omit [Fintype X] [DecidableEq X] [DecidableLE X] in
/-- Incomparable elements are distinct. -/
theorem Incomp.ne {x y : X} (h : Incomp x y) : x ≠ y := by
  rintro rfl; exact h.1 le_rfl

/-- **Balanced pairs are symmetric.**  `{x,y}` is balanced iff `{y,x}` is: the
two defining inequalities swap roles under the partition identity
`e(P,x<y) + e(P,y<x) = e(P)`. -/
theorem isBalancedPair_comm {x y : X} : IsBalancedPair x y ↔ IsBalancedPair y x := by
  have key : ∀ a b : X, Incomp a b →
      (numLinExts (X := X) ≤ 3 * numBefore a b ∧
        3 * numBefore a b ≤ 2 * numLinExts (X := X)) →
      (numLinExts (X := X) ≤ 3 * numBefore b a ∧
        3 * numBefore b a ≤ 2 * numLinExts (X := X)) := by
    intro a b hab h
    have hpart := numBefore_add_numBefore a b hab.ne
    have hpart' : numBefore b a = numLinExts (X := X) - numBefore a b := by omega
    obtain ⟨h1, h2⟩ := h
    have hle : numBefore a b ≤ numLinExts (X := X) := numBefore_le_numLinExts a b hab.ne
    constructor <;> omega
  constructor
  · intro h; exact ⟨h.1.symm, key x y h.1 h.2⟩
  · intro h; exact ⟨h.1.symm, key y x h.1 h.2⟩

/-- **Min-form of the balanced-pair predicate.**  `{x,y}` is balanced iff
`e(P) ≤ 3 · min(e(P,x<y), e(P,y<x))`.  This is the form matching the literature's
`δ(P) = max_{x∥y} min(δ(x,y), δ(y,x)) ≥ 1/3`: an incomparable pair is balanced
exactly when the *smaller* side is at least a third.  (Equivalent to the
two-sided `[1/3,2/3]` definition via the partition identity.) -/
theorem isBalancedPair_iff_le_three_min {x y : X} :
    IsBalancedPair x y ↔
      Incomp x y ∧ numLinExts (X := X) ≤ 3 * min (numBefore x y) (numBefore y x) := by
  unfold IsBalancedPair
  constructor
  · rintro ⟨hinc, h1, h2⟩
    refine ⟨hinc, ?_⟩
    have hpart := numBefore_add_numBefore x y hinc.ne
    rcases le_total (numBefore x y) (numBefore y x) with hmin | hmin
    · rw [min_eq_left hmin]; exact h1
    · rw [min_eq_right hmin]; omega
  · rintro ⟨hinc, h⟩
    have hpart := numBefore_add_numBefore x y hinc.ne
    have hx := min_le_left (numBefore x y) (numBefore y x)
    have hy := min_le_right (numBefore x y) (numBefore y x)
    exact ⟨hinc, by omega, by omega⟩

/-- A poset that is a chain (totally ordered) satisfies the conjecture
vacuously: it has no incomparable pair, so the hypothesis `IsNotChain` fails. -/
theorem oneThirdTwoThirdsFor_of_total
    (htot : ∀ a b : X, a ≤ b ∨ b ≤ a) : OneThirdTwoThirdsFor (X := X) := by
  rintro ⟨x, y, hx, hy⟩
  rcases htot x y with h | h
  · exact absurd h hx
  · exact absurd h hy

omit [Fintype X] [DecidableEq X] in
/-- `IsNotChain` is exactly the failure of totality. -/
theorem isNotChain_iff_not_total :
    IsNotChain (X := X) ↔ ¬ (∀ a b : X, a ≤ b ∨ b ≤ a) := by
  constructor
  · rintro ⟨x, y, hx, hy⟩ htot
    rcases htot x y with h | h
    · exact hx h
    · exact hy h
  · intro h
    by_contra hcon
    apply h
    intro a b
    by_contra hab
    push_neg at hab
    exact hcon ⟨a, b, hab.1, hab.2⟩

end OneThirdTwoThirds
