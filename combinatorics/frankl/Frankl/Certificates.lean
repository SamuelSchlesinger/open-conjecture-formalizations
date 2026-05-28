import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Finite Certificate Checkers

Reference: `combinatorics/frankl/research/checklist.md`

This file begins the Lean side of the certificate pipeline.  The JSON files in
`research/` are external payloads; the intended next step is to translate their
decimal/interval rows into rational lower-bound rows of the form checked here.

The checker below is intentionally generic: if every row carries a rational
lower bound above a required floor, then the finite row table is accepted.
-/

set_option autoImplicit false

namespace Frankl

/-- One finite certificate row: a rational grid point together with a rational
lower bound for the expression being checked there. -/
structure LowerBoundRow where
  xNum : Int
  xDen : Nat
  lowerBound : ℚ

namespace LowerBoundRow

/-- The rational grid point represented by a row.  If `xDen = 0`, this junk
value is `0`; valid certificates should use `validPoint`. -/
def x (row : LowerBoundRow) : ℚ :=
  row.xNum / row.xDen

def validPoint (row : LowerBoundRow) : Prop :=
  row.xDen ≠ 0

/-- Boolean row check against a rational floor. -/
def passes (floor : ℚ) (row : LowerBoundRow) : Bool :=
  decide (floor ≤ row.lowerBound)

theorem passes_eq_true_iff {floor : ℚ} {row : LowerBoundRow} :
    row.passes floor = true ↔ floor ≤ row.lowerBound := by
  unfold passes
  exact decide_eq_true_iff

end LowerBoundRow

/-- Propositional meaning of a finite lower-bound table. -/
def LowerBoundRowsPass (floor : ℚ) (rows : List LowerBoundRow) : Prop :=
  ∀ row ∈ rows, floor ≤ row.lowerBound

/-- Boolean finite lower-bound checker. -/
def checkLowerBoundRows (floor : ℚ) (rows : List LowerBoundRow) : Bool :=
  rows.all fun row => row.passes floor

theorem checkLowerBoundRows_sound {floor : ℚ} {rows : List LowerBoundRow}
    (h : checkLowerBoundRows floor rows = true) :
    LowerBoundRowsPass floor rows := by
  unfold LowerBoundRowsPass
  induction rows with
  | nil =>
      intro row hrow
      simp at hrow
  | cons head tail ih =>
      intro row hrow
      simp [checkLowerBoundRows] at h
      rcases h with ⟨hHead, hTail⟩
      simp at hrow
      rcases hrow with rfl | hrowTail
      ·
        exact LowerBoundRow.passes_eq_true_iff.mp hHead
      · exact LowerBoundRow.passes_eq_true_iff.mp (hTail row hrowTail)

theorem checkLowerBoundRows_complete {floor : ℚ} {rows : List LowerBoundRow}
    (h : LowerBoundRowsPass floor rows) :
    checkLowerBoundRows floor rows = true := by
  induction rows with
  | nil =>
      simp [checkLowerBoundRows]
  | cons head tail ih =>
      have hHead : floor ≤ head.lowerBound := h head (by simp)
      have hTail : LowerBoundRowsPass floor tail := by
        intro row hrow
        exact h row (by simp [hrow])
      simp [checkLowerBoundRows]
      constructor
      · exact LowerBoundRow.passes_eq_true_iff.mpr hHead
      · intro row hrow
        exact LowerBoundRow.passes_eq_true_iff.mpr (hTail row hrow)

theorem checkLowerBoundRows_eq_true_iff {floor : ℚ} {rows : List LowerBoundRow} :
    checkLowerBoundRows floor rows = true ↔ LowerBoundRowsPass floor rows :=
  ⟨checkLowerBoundRows_sound, checkLowerBoundRows_complete⟩

end Frankl
