import Frankl.AHSData
import Frankl.AHSFormula
import Mathlib.Tactic

/-!
# AHS Interval Certificate Interfaces

Reference: `combinatorics/frankl/research/ahs_hinge_certificate.json`

This file gives the Lean-side shape of the interval certificates used in the
Alweiss-Huang-Sellke hinge audit.  The hard transcendental work is still
external: future files must prove that the rational rows really bound the
logarithmic expressions.  Once those row bounds are available, the generic
lemmas here assemble them over an interval.
-/

set_option autoImplicit false

namespace Frankl

/-- A rational interval row together with a rational lower floor. -/
structure AHSIntervalRow where
  left : ℚ
  right : ℚ
  lowerFloor : ℚ

namespace AHSIntervalRow

/-- The real interval represented by a rational row. -/
def interval (row : AHSIntervalRow) : Set ℝ :=
  Set.Icc (row.left : ℝ) (row.right : ℝ)

/-- The row asserts that `f` is bounded below by its rational floor throughout
the represented interval. -/
def BoundsBelow (row : AHSIntervalRow) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ row.interval, (row.lowerFloor : ℝ) ≤ f x

end AHSIntervalRow

/-- A finite row table covers a target interval. -/
def AHSRowsCover (rows : List AHSIntervalRow) (lo hi : ℝ) : Prop :=
  ∀ x ∈ Set.Icc lo hi, ∃ row ∈ rows, x ∈ row.interval

/-- Every row in a finite table supplies its advertised lower bound. -/
def AHSRowsBoundBelow (rows : List AHSIntervalRow) (f : ℝ → ℝ) : Prop :=
  ∀ row ∈ rows, row.BoundsBelow f

/-- If rows cover an interval and each row has a floor at least `floor`, then
the function is bounded below by `floor` on the covered interval. -/
theorem ahsRows_lower_bound_on_interval {rows : List AHSIntervalRow}
    {f : ℝ → ℝ} {lo hi floor : ℝ}
    (hcover : AHSRowsCover rows lo hi)
    (hrows : AHSRowsBoundBelow rows f)
    (hfloors : ∀ row ∈ rows, floor ≤ (row.lowerFloor : ℝ)) :
    ∀ x ∈ Set.Icc lo hi, floor ≤ f x := by
  intro x hx
  rcases hcover x hx with ⟨row, hrow, hxrow⟩
  exact le_trans (hfloors row hrow) (hrows row hrow x hxrow)

/-- A grid row: a rational point, a rational radius, and a rational lower
floor for the function value at that point. -/
structure AHSGridRow where
  point : ℚ
  radius : ℚ
  valueFloor : ℚ

/-- The target interval is covered by grid balls whose centers also lie in the
target interval. -/
def AHSGridRowsCover (rows : List AHSGridRow) (lo hi : ℝ) : Prop :=
  ∀ x ∈ Set.Icc lo hi,
    ∃ row ∈ rows,
      (row.point : ℝ) ∈ Set.Icc lo hi ∧ |x - (row.point : ℝ)| ≤ (row.radius : ℝ)

/-- Pointwise lower-bound payload for a grid table. -/
def AHSGridRowsPointBound (rows : List AHSGridRow) (f : ℝ → ℝ) : Prop :=
  ∀ row ∈ rows, (row.valueFloor : ℝ) ≤ f (row.point : ℝ)

/-- Each grid row has enough clearance to absorb the Lipschitz loss over its
radius. -/
def AHSGridRowsClearLipschitzLoss (rows : List AHSGridRow)
    (floor K : ℝ) : Prop :=
  ∀ row ∈ rows, floor ≤ (row.valueFloor : ℝ) - K * (row.radius : ℝ)

/-- A local Lipschitz condition on a closed interval. -/
def LipschitzOnIcc (f : ℝ → ℝ) (K lo hi : ℝ) : Prop :=
  ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi, |f x - f y| ≤ K * |x - y|

/-- Grid values plus a Lipschitz constant give a lower bound everywhere on the
covered interval. -/
theorem gridRows_lipschitz_lower_bound {rows : List AHSGridRow}
    {f : ℝ → ℝ} {K lo hi floor : ℝ}
    (hK : 0 ≤ K)
    (hcover : AHSGridRowsCover rows lo hi)
    (hpoint : AHSGridRowsPointBound rows f)
    (hclear : AHSGridRowsClearLipschitzLoss rows floor K)
    (hlip : LipschitzOnIcc f K lo hi) :
    ∀ x ∈ Set.Icc lo hi, floor ≤ f x := by
  intro x hx
  rcases hcover x hx with ⟨row, hrow, hrowPoint, hdist⟩
  have hpointLower : (row.valueFloor : ℝ) ≤ f (row.point : ℝ) :=
    hpoint row hrow
  have hdist' : |(row.point : ℝ) - x| ≤ (row.radius : ℝ) := by
    simpa [abs_sub_comm] using hdist
  have hKdist : K * |(row.point : ℝ) - x| ≤ K * (row.radius : ℝ) :=
    mul_le_mul_of_nonneg_left hdist' hK
  have hdiffAbs :
      |f (row.point : ℝ) - f x| ≤ K * |(row.point : ℝ) - x| :=
    hlip (row.point : ℝ) hrowPoint x hx
  have hdiff : f (row.point : ℝ) - f x ≤ K * (row.radius : ℝ) := by
    calc
      f (row.point : ℝ) - f x ≤ |f (row.point : ℝ) - f x| := le_abs_self _
      _ ≤ K * |(row.point : ℝ) - x| := hdiffAbs
      _ ≤ K * (row.radius : ℝ) := hKdist
  have hfx : (row.valueFloor : ℝ) - K * (row.radius : ℝ) ≤ f x := by
    linarith
  exact le_trans (hclear row hrow) hfx

/-- The AHS `I1` endpoint used by the audit. -/
noncomputable def ahsI1Lo : ℝ :=
  ahsPhi

/-- The AHS `I1` upper endpoint used by the audit. -/
noncomputable def ahsI1Hi : ℝ :=
  77 / 100

/-- The AHS `I2` lower endpoint used by the audit. -/
noncomputable def ahsI2Lo : ℝ :=
  76 / 100

/-- The AHS `I2` upper endpoint used by the audit. -/
noncomputable def ahsI2Hi : ℝ :=
  98 / 100

/-- The AHS `I3` lower endpoint used by the audit. -/
noncomputable def ahsI3Lo : ℝ :=
  98 / 100

/-- The AHS `I3` upper endpoint used by the audit. -/
noncomputable def ahsI3Hi : ℝ :=
  1

/-- The `I1` grid-row bridge: once Lean knows the grid values and the
Lipschitz constant for `ahsL`, the rational floor holds throughout `I1`. -/
theorem ahsI1_rows_lipschitz_imply_L_floor {rows : List AHSGridRow}
    (hcover : AHSGridRowsCover rows ahsI1Lo ahsI1Hi)
    (hpoint : AHSGridRowsPointBound rows ahsL)
    (hclear :
      AHSGridRowsClearLipschitzLoss rows (ahsI1RequiredFloor : ℝ) (31 / 2))
    (hlip : LipschitzOnIcc ahsL (31 / 2) ahsI1Lo ahsI1Hi) :
    ∀ x ∈ Set.Icc ahsI1Lo ahsI1Hi, (ahsI1RequiredFloor : ℝ) ≤ ahsL x := by
  exact gridRows_lipschitz_lower_bound (by norm_num) hcover hpoint hclear hlip

/-- The remaining analytic bridge for `I1`: if the certified positive lower
bound on `ahsL` implies the hinge inequality, then the grid certificate proves
the hinge inequality on `I1`. -/
theorem ahsI1_rows_lipschitz_imply_G_nonneg {rows : List AHSGridRow}
    (hbridge :
      ∀ x ∈ Set.Icc ahsI1Lo ahsI1Hi, (ahsI1RequiredFloor : ℝ) ≤ ahsL x → 0 ≤ ahsG x)
    (hcover : AHSGridRowsCover rows ahsI1Lo ahsI1Hi)
    (hpoint : AHSGridRowsPointBound rows ahsL)
    (hclear :
      AHSGridRowsClearLipschitzLoss rows (ahsI1RequiredFloor : ℝ) (31 / 2))
    (hlip : LipschitzOnIcc ahsL (31 / 2) ahsI1Lo ahsI1Hi) :
    ∀ x ∈ Set.Icc ahsI1Lo ahsI1Hi, 0 ≤ ahsG x := by
  intro x hx
  exact hbridge x hx
    (ahsI1_rows_lipschitz_imply_L_floor hcover hpoint hclear hlip x hx)

/-- A finite monotone-chain row used on the AHS middle interval. -/
structure AHSChainRow where
  left : ℚ
  right : ℚ
  gapFloor : ℚ

/-- A chain table covers an interval, with every selected row endpoint also in
the interval. -/
def AHSChainRowsCover (rows : List AHSChainRow) (lo hi : ℝ) : Prop :=
  ∀ x ∈ Set.Icc lo hi,
    ∃ row ∈ rows,
      (row.left : ℝ) ∈ Set.Icc lo hi ∧
      (row.right : ℝ) ∈ Set.Icc lo hi ∧
      (row.left : ℝ) ≤ x ∧ x ≤ (row.right : ℝ)

/-- A nonincreasing condition on a closed interval, stated directly to keep
the certificate interface independent of library naming choices. -/
def NonincreasingOnIcc (f : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi, x ≤ y → f y ≤ f x

/-- The `I2` monotone-chain bridge: row gaps plus monotonicity imply
`g1 >= g2` across the middle interval. -/
theorem ahsI2_monotone_chain_implies_g1_ge_g2 {rows : List AHSChainRow}
    (hcover : AHSChainRowsCover rows ahsI2Lo ahsI2Hi)
    (hgaps :
      ∀ row ∈ rows,
        0 ≤ (row.gapFloor : ℝ) ∧
          (row.gapFloor : ℝ) ≤ ahsG1 (row.right : ℝ) - ahsG2 (row.left : ℝ))
    (hg1 : NonincreasingOnIcc ahsG1 ahsI2Lo ahsI2Hi)
    (hg2 : NonincreasingOnIcc ahsG2 ahsI2Lo ahsI2Hi) :
    ∀ x ∈ Set.Icc ahsI2Lo ahsI2Hi, ahsG2 x ≤ ahsG1 x := by
  intro x hx
  rcases hcover x hx with ⟨row, hrow, hleft, hright, hle, hxr⟩
  have hgap : ahsG2 (row.left : ℝ) ≤ ahsG1 (row.right : ℝ) := by
    have hrowGap := hgaps row hrow
    linarith
  have hg1x : ahsG1 (row.right : ℝ) ≤ ahsG1 x :=
    hg1 x hx (row.right : ℝ) hright hxr
  have hg2x : ahsG2 x ≤ ahsG2 (row.left : ℝ) :=
    hg2 (row.left : ℝ) hleft x hx hle
  linarith

/-- The final AHS tail bridge: the current rational positive margin is enough
once the analytic tail reduction is proved in Lean. -/
theorem ahsI3_tail_margin_implies_G_nonneg
    (htail :
      ∀ x ∈ Set.Icc ahsI3Lo ahsI3Hi,
        0 < (ahsI3MarginRationalFloor : ℝ) → 0 ≤ ahsG x) :
    ∀ x ∈ Set.Icc ahsI3Lo ahsI3Hi, 0 ≤ ahsG x := by
  intro x hx
  exact htail x hx (by exact_mod_cast ahsI3MarginRationalFloor_pos)

/-- A tiny toy interval row used to exercise the row-cover interface. -/
def toyUnitRow : AHSIntervalRow :=
  { left := 0, right := 1, lowerFloor := 0 }

theorem toyUnitRow_bounds_const_one :
    toyUnitRow.BoundsBelow (fun _ => (1 : ℝ)) := by
  intro x hx
  norm_num [toyUnitRow, AHSIntervalRow.BoundsBelow]

theorem toyUnitRow_covers_unit :
    AHSRowsCover [toyUnitRow] 0 1 := by
  intro x hx
  refine ⟨toyUnitRow, by simp, ?_⟩
  simpa [toyUnitRow, AHSIntervalRow.interval] using hx

theorem toyUnitRow_floor_nonnegative :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) x := by
  refine ahsRows_lower_bound_on_interval toyUnitRow_covers_unit ?_ ?_
  · intro row hrow
    simp at hrow
    subst row
    exact toyUnitRow_bounds_const_one
  · intro row hrow
    simp at hrow
    subst row
    norm_num [toyUnitRow]

end Frankl
