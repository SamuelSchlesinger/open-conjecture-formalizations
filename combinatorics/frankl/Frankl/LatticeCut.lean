import Frankl.Lattice
import Mathlib.Order.LatticeIntervals

/-!
# Frankl's lattice conjecture reduces along a cut element

Reference: `research/frankl_negative_space_round.md` (vertical / ordinal-sum
decomposition).

A **cut element** `c` of a lattice `L` is comparable to every element
(`∀ x, x ≤ c ∨ c ≤ x`); it splits `L` vertically into `↓c` and the filter
`↑c = Set.Ici c`, glued at `c`.  A join-irreducible Frankl witness of the filter
`↑c` **lifts** to `L`:

* a join-irreducible `j` of `↑c` (necessarily `j ≠ c`, since `c = ⊥` of `↑c` is
  not join-irreducible) is join-irreducible in `L` — its lower covers all lie
  `≥ c` by the cut property;
* its up-set is unchanged, `{x : L // ↑j ≤ x} ≃ {y : ↑c // j ≤ y}`, because
  everything above `↑j ≥ c` already lies in `↑c`;
* and `|↑c| ≤ |L|`, so the `½`-bound is preserved.

Hence Frankl for the strictly smaller filter `↑c` implies Frankl for `L`, and the
lattice conjecture reduces to the **vertically-indecomposable** lattices (no cut
element strictly between `⊥` and `⊤`).  Together with the direct-product
reduction (`Frankl.LatticeProduct`) this narrows the conjecture to lattices that
are both directly and vertically indecomposable.  Like the product reduction this
is a structural argument, not a local witness-selection.
-/

set_option autoImplicit false

namespace Frankl

open Set

variable {L : Type*} [Lattice L]

/-- A join-irreducible of the filter `↑c` lifts to a join-irreducible of `L`,
when `c` is a cut element. -/
theorem supIrred_val_of_cut {c : L} (hcut : ∀ x : L, x ≤ c ∨ c ≤ x)
    {j : Set.Ici c} (hj : SupIrred j) : SupIrred ((j : L)) := by
  have hcj : c ≤ (j : L) := mem_Ici.mp j.2
  refine ⟨?_, ?_⟩
  · -- `(j : L)` is not minimal because `j` is not minimal in `↑c`.
    intro hmin
    refine hj.1 (fun y hy => ?_)
    have h1 : (y : L) ≤ (j : L) := Subtype.coe_le_coe.mpr hy
    exact Subtype.coe_le_coe.mp (hmin h1)
  · rintro a b hab
    rcases hcut a with hac | hca
    · rcases hcut b with hbc | hcb
      · -- `a, b ≤ c` forces `(j : L) = c`, but then `j` is the bottom of `↑c`.
        exfalso
        have hjc : (j : L) ≤ c := by rw [← hab]; exact sup_le hac hbc
        have hjeq : (j : L) = c := le_antisymm hjc hcj
        refine hj.1 (fun y _ => ?_)
        have : (j : L) ≤ (y : L) := by rw [hjeq]; exact mem_Ici.mp y.2
        exact Subtype.coe_le_coe.mp this
      · -- `a ≤ c ≤ b` ⇒ `a ⊔ b = b = (j : L)`.
        right
        rw [sup_eq_right.mpr (hac.trans hcb)] at hab
        exact hab
    · rcases hcut b with hbc | hcb
      · -- `b ≤ c ≤ a` ⇒ `a ⊔ b = a = (j : L)`.
        left
        rw [sup_eq_left.mpr (hbc.trans hca)] at hab
        exact hab
      · -- `c ≤ a` and `c ≤ b`: lift to `↑c` and use irreducibility of `j` there.
        have hsup : (⟨a, mem_Ici.mpr hca⟩ : Set.Ici c) ⊔ ⟨b, mem_Ici.mpr hcb⟩ = j :=
          Subtype.ext hab
        rcases hj.2 hsup with h | h
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (congrArg Subtype.val h)

/-- The up-set of `(j : L)` equals the up-set of `j` inside the filter `↑c`. -/
def upSetCutEquiv {c : L} (j : Set.Ici c) :
    {x : L // (j : L) ≤ x} ≃ {y : Set.Ici c // j ≤ y} where
  toFun := fun x => ⟨⟨x.1, mem_Ici.mpr ((mem_Ici.mp j.2).trans x.2)⟩,
    Subtype.coe_le_coe.mp x.2⟩
  invFun := fun y => ⟨y.1.1, Subtype.coe_le_coe.mpr y.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **Cut lemma.**  If `c` is a cut element of `L` and the filter `↑c` carries a
Frankl witness, then so does `L`. -/
theorem franklLattice_witness_of_cut [Finite L] {c : L}
    (hcut : ∀ x : L, x ≤ c ∨ c ≤ x)
    (h : ∃ j : Set.Ici c, SupIrred j ∧
      2 * Nat.card {y : Set.Ici c // j ≤ y} ≤ Nat.card (Set.Ici c)) :
    ∃ j : L, SupIrred j ∧ 2 * Nat.card {x : L // j ≤ x} ≤ Nat.card L := by
  obtain ⟨j, hj, hjc⟩ := h
  refine ⟨(j : L), supIrred_val_of_cut hcut hj, ?_⟩
  rw [Nat.card_congr (upSetCutEquiv j)]
  calc 2 * Nat.card {y : Set.Ici c // j ≤ y}
      ≤ Nat.card (Set.Ici c) := hjc
    _ ≤ Nat.card L := Nat.card_le_card_of_injective _ Subtype.val_injective

end Frankl
