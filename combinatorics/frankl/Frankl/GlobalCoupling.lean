import Frankl.Probability
import Mathlib.Tactic

/-!
# Global Uniform Couplings

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file starts the Lean API for the global coupled-kernel program.  A finite
union-closed family is represented by an index type `ι` of members together
with a map `member : ι → Finset α`.  A global coupling is a probability weight
on `ι × ι` with uniform left and right marginals.
-/

set_option autoImplicit false

namespace Frankl

open scoped BigOperators

/-- A probability coupling of two uniform samples from a finite index type. -/
structure UniformCoupling (ι : Type*) [Fintype ι] where
  weight : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ weight i j
  left_marginal : ∀ i, ∑ j, weight i j = (Fintype.card ι : ℝ)⁻¹
  right_marginal : ∀ j, ∑ i, weight i j = (Fintype.card ι : ℝ)⁻¹

namespace UniformCoupling

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- The total mass of a uniform coupling.  For nonempty index types this is
`1`; the formula is kept in reciprocal form to avoid adding a nonemptiness
hypothesis to the definition. -/
noncomputable def totalMass (C : UniformCoupling ι) : ℝ :=
  ∑ i, ∑ j, C.weight i j

theorem totalMass_eq_card_mul_inv (C : UniformCoupling ι) :
    C.totalMass = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)⁻¹ := by
  unfold totalMass
  simp [C.left_marginal]

/-- OR-incidence of coordinate `x` for the pair of indexed family members
`i,j`. -/
def orIncidence (member : ι → Finset α) (x : α) (i j : ι) : ℝ :=
  if x ∈ member i ∪ member j then 1 else 0

/-- Coordinate OR marginal under a global coupling. -/
noncomputable def coordinateOrMarginal (C : UniformCoupling ι)
    (member : ι → Finset α) (x : α) : ℝ :=
  ∑ i, ∑ j, C.weight i j * orIncidence member x i j

/-- Coordinate atom `P(X_x = 0, Y_x = 1)` induced by a global coupling. -/
noncomputable def coordinateAtom01 (C : UniformCoupling ι)
    (member : ι → Finset α) (x : α) : ℝ :=
  ∑ i, ∑ j, C.weight i j *
    (if x ∉ member i ∧ x ∈ member j then 1 else 0)

/-- Coordinate atom `P(X_x = 1, Y_x = 0)` induced by a global coupling. -/
noncomputable def coordinateAtom10 (C : UniformCoupling ι)
    (member : ι → Finset α) (x : α) : ℝ :=
  ∑ i, ∑ j, C.weight i j *
    (if x ∈ member i ∧ x ∉ member j then 1 else 0)

/-- Coordinate atom `P(X_x = 1, Y_x = 1)` induced by a global coupling. -/
noncomputable def coordinateAtom11 (C : UniformCoupling ι)
    (member : ι → Finset α) (x : α) : ℝ :=
  ∑ i, ∑ j, C.weight i j *
    (if x ∈ member i ∧ x ∈ member j then 1 else 0)

theorem coordinateOrMarginal_eq_atoms (C : UniformCoupling ι)
    (member : ι → Finset α) (x : α) :
    C.coordinateOrMarginal member x =
      C.coordinateAtom01 member x +
        C.coordinateAtom10 member x +
        C.coordinateAtom11 member x := by
  unfold coordinateOrMarginal coordinateAtom01 coordinateAtom10 coordinateAtom11
  calc
    (∑ i, ∑ j, C.weight i j * orIncidence member x i j) =
        ∑ i, ∑ j,
          ((C.weight i j * (if x ∉ member i ∧ x ∈ member j then 1 else 0)) +
            (C.weight i j * (if x ∈ member i ∧ x ∉ member j then 1 else 0)) +
            (C.weight i j * (if x ∈ member i ∧ x ∈ member j then 1 else 0))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      by_cases hxi : x ∈ member i <;> by_cases hxj : x ∈ member j <;>
        simp [orIncidence, hxi, hxj]
    _ =
        (∑ i, ∑ j, C.weight i j *
            (if x ∉ member i ∧ x ∈ member j then 1 else 0)) +
          (∑ i, ∑ j, C.weight i j *
              (if x ∈ member i ∧ x ∉ member j then 1 else 0)) +
          (∑ i, ∑ j, C.weight i j *
              (if x ∈ member i ∧ x ∈ member j then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, add_assoc]

theorem coordinateOrMarginal_eq_twoBernoulli_orMarginal
    (C : UniformCoupling ι) (member : ι → Finset α) (x : α)
    (c : TwoBernoulliCoupling)
    (h01 : c.p01 = C.coordinateAtom01 member x)
    (h10 : c.p10 = C.coordinateAtom10 member x)
    (h11 : c.p11 = C.coordinateAtom11 member x) :
    C.coordinateOrMarginal member x = c.orMarginal := by
  rw [coordinateOrMarginal_eq_atoms, ← h01, ← h10, ← h11]
  rfl

theorem coordinateOrMarginal_congr_orIncidence
    (C : UniformCoupling ι)
    {member₁ member₂ : ι → Finset α} {x : α}
    (h :
      ∀ i j,
        orIncidence member₁ x i j = orIncidence member₂ x i j) :
    C.coordinateOrMarginal member₁ x = C.coordinateOrMarginal member₂ x := by
  unfold coordinateOrMarginal
  simp [h]

/-- A coupling centers every coordinate in a selected finite set. -/
def CentersCoordinates (C : UniformCoupling ι)
    (member : ι → Finset α) (coords : Finset α) : Prop :=
  ∀ x ∈ coords, C.coordinateOrMarginal member x = 1 / 2

/-- The center polytope of a selected coordinate set, represented as a predicate
on uniform couplings. -/
def centerPolytope (member : ι → Finset α) (coords : Finset α) :
    Set (UniformCoupling ι) :=
  { C | C.CentersCoordinates member coords }

theorem mem_centerPolytope_iff {member : ι → Finset α} {coords : Finset α}
    {C : UniformCoupling ι} :
    C ∈ centerPolytope member coords ↔ C.CentersCoordinates member coords := by
  rfl

/-- Coordinate-order face: coordinate `x` is pointwise dominated by
coordinate `y` on the indexed family. -/
def CoordinateLe (member : ι → Finset α) (x y : α) : Prop :=
  ∀ i, x ∈ member i → y ∈ member i

omit [Fintype ι] in
theorem orIncidence_le_of_coordinateLe {member : ι → Finset α} {x y : α}
    (hxy : CoordinateLe member x y) (i j : ι) :
    orIncidence member x i j ≤ orIncidence member y i j := by
  unfold orIncidence
  by_cases hx : x ∈ member i ∪ member j
  · have hy : y ∈ member i ∪ member j := by
      rcases (by simpa using hx : x ∈ member i ∨ x ∈ member j) with hxi | hxj
      · exact by simp [hxy i hxi]
      · exact by simp [hxy j hxj]
    simp [hx, hy]
  · by_cases hy : y ∈ member i ∪ member j
    · simp [hx, hy]
    · simp [hx, hy]

theorem coordinateOrMarginal_le_of_coordinateLe
    (C : UniformCoupling ι) {member : ι → Finset α} {x y : α}
    (hxy : CoordinateLe member x y) :
    C.coordinateOrMarginal member x ≤ C.coordinateOrMarginal member y := by
  unfold coordinateOrMarginal
  refine Finset.sum_le_sum ?_
  intro i hi
  refine Finset.sum_le_sum ?_
  intro j hj
  exact mul_le_mul_of_nonneg_left
    (orIncidence_le_of_coordinateLe hxy i j)
    (C.nonneg i j)

end UniformCoupling

end Frankl
