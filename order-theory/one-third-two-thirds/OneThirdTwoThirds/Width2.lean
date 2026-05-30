import OneThirdTwoThirds.Basic
import Mathlib.Order.Antichain

/-!
# The 1/3–2/3 conjecture — width and the Linial frontier

The *width* of a poset is the largest size of an antichain (a set of pairwise
incomparable elements).  This file records the width hierarchy and states the
classical width-based results, marking precisely what is proved here and what is
a known but not-yet-formalized target.

* **Width ≤ 1 = chains** (`widthLE_one_iff_total`): proved, and such posets
  satisfy the conjecture vacuously (`oneThirdTwoThirdsFor_of_widthLE_one`).
* **Width ≤ 2** — Linial (1984) proved the conjecture for width ≤ 2, and that
  `1/3` is best possible there.  We state this precisely as `LinialWidthTwo`;
  its proof is a genuine combinatorial argument (not a finite check) and is left
  as an open formalization target.  Sah (2021) sharpened the width-2 constant to
  `≈ 0.3388` and exhibited width-2 families with `δ → ≈ 0.3488`.

The quantitative general frontier (stated in the README, not here, because the
record constant is irrational): Kahn–Saks (1984) `δ(P) ≥ 3/11 ≈ 0.273`, improved
to the current record `δ(P) ≥ (5−√5)/10 ≈ 0.2764` by Brightwell–Felsner–Trotter
(1995).  The gap to `1/3` is the open problem.

The proved-here reductions that *do* apply across all widths are duality
(`Duality`) and the twin/symmetry case (`Symmetry`).
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {X : Type*} [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]

/-- `WidthLE k`: every antichain has at most `k` elements (the poset has width
`≤ k`). -/
def WidthLE (k : ℕ) : Prop :=
  ∀ s : Finset X, IsAntichain (· ≤ ·) (s : Set X) → s.card ≤ k

omit [Fintype X] [DecidableLE X] in
/-- **Width ≤ 1 means the poset is a chain.**  An antichain of two distinct
elements would be an incomparable pair, so width `≤ 1` forces totality; and a
total order has no two-element antichain. -/
theorem widthLE_one_iff_total :
    WidthLE (X := X) 1 ↔ ∀ a b : X, a ≤ b ∨ b ≤ a := by
  constructor
  · intro hw a b
    by_contra hcon
    push_neg at hcon
    obtain ⟨hab, hba⟩ := hcon
    have hne : a ≠ b := by rintro rfl; exact hab le_rfl
    have hanti : IsAntichain (· ≤ ·) (({a, b} : Finset X) : Set X) := by
      intro p hp q hq hpq
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        first | exact absurd rfl hpq | exact hab | exact hba
    have hcard : ({a, b} : Finset X).card = 2 := Finset.card_pair hne
    have := hw {a, b} hanti
    omega
  · intro htot s hs
    by_contra hcon
    push_neg at hcon
    -- card ≥ 2, so there are two distinct elements; they are comparable, breaking antichain
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp (by omega)
    have hab : ¬ a ≤ b := hs (by simpa using ha) (by simpa using hb) hne
    rcases htot a b with h | h
    · exact hab h
    · exact hs (by simpa using hb) (by simpa using ha) (Ne.symm hne) h

/-- A poset of width `≤ 1` (a chain) satisfies the conjecture vacuously. -/
theorem oneThirdTwoThirdsFor_of_widthLE_one (hw : WidthLE (X := X) 1) :
    OneThirdTwoThirdsFor (X := X) :=
  oneThirdTwoThirdsFor_of_total (widthLE_one_iff_total.mp hw)

/-- **Linial's width-2 theorem (1984)**, stated precisely as a target: every
finite poset of width `≤ 2` satisfies the 1/3–2/3 conjecture.

This is a *known theorem* (Linial, *The information-theoretic bound is good for
merging*, SIAM J. Comput. 1984); its proof is a genuine combinatorial/inductive
argument, not a finite computation, and is **not** formalized here — it is left
as the next analytic milestone.  We state it so the target is explicit and
type-checked.  (Cf. `SmallCases.V3_balance_tight`: the width-2 poset `V3` shows
`1/3` is best possible already at width 2.) -/
def LinialWidthTwo : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X],
    WidthLE (X := X) 2 → OneThirdTwoThirdsFor (X := X)

end OneThirdTwoThirds
