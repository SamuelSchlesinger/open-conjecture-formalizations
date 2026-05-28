import Frankl.Basic
import Mathlib.Tactic

/-!
# Fiber Lemmas for Frankl Obstruction Analysis

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file contains the Lean-ready core of the fiber analysis used in the
English obstruction note.  The main point formalized here is that if a fiber
has a maximum auxiliary set, then any bottom-fiber set whose union with that
maximum remains in the fiber must be contained in the maximum.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Frankl

variable {α : Type*} [DecidableEq α]

/-- `M` is a maximum member of a finite family of finite sets. -/
def HasMaximum (G : Finset (Finset α)) (M : Finset α) : Prop :=
  M ∈ G ∧ ∀ A ∈ G, A ⊆ M

theorem HasMaximum.mem {G : Finset (Finset α)} {M : Finset α}
    (hM : HasMaximum G M) :
    M ∈ G :=
  hM.1

theorem HasMaximum.subset {G : Finset (Finset α)} {M A : Finset α}
    (hM : HasMaximum G M) (hA : A ∈ G) :
    A ⊆ M :=
  hM.2 A hA

/-- A one-member family has its unique member as maximum. -/
theorem hasMaximum_singleton (M : Finset α) :
    HasMaximum ({M} : Finset (Finset α)) M := by
  refine ⟨by simp, ?_⟩
  intro A hA
  have hAM : A = M := by
    simpa using hA
  subst A
  exact subset_rfl

/-- In a two-member union-closed family, the union of the two displayed
members is a maximum member. -/
theorem hasMaximum_pair_union_of_union_closed (A B : Finset α)
    (hG : IsUnionClosed ({A, B} : Finset (Finset α))) :
    HasMaximum ({A, B} : Finset (Finset α)) (A ∪ B) := by
  have hAuB : A ∪ B ∈ ({A, B} : Finset (Finset α)) := by
    exact hG A (by simp) B (by simp)
  refine ⟨hAuB, ?_⟩
  intro C hC x hxC
  have hCAorB : C = A ∨ C = B := by
    simpa using hC
  rcases hCAorB with hCA | hCB
  · subst C
    simp [hxC]
  · subst C
    simp [hxC]

/-- Starting from a member of a union-closed family, unioning any finite
subfamily of members stays in the family. -/
theorem union_biUnion_mem_of_subset {F G : Finset (Finset α)} {A : Finset α}
    (hF : IsUnionClosed F) (hG : G ⊆ F) (hA : A ∈ F) :
    A ∪ G.biUnion id ∈ F := by
  revert hG
  refine Finset.induction_on G ?base ?step
  · intro _hG
    simpa using hA
  · intro B G hBG hIH hG
    have hGsubset : G ⊆ F := by
      intro C hC
      exact hG (Finset.mem_insert_of_mem hC)
    have hB : B ∈ F := hG (Finset.mem_insert_self B G)
    have hAcc : A ∪ G.biUnion id ∈ F := hIH hGsubset
    have hUnion : (A ∪ G.biUnion id) ∪ B ∈ F := hF (A ∪ G.biUnion id) hAcc B hB
    have hEq : A ∪ (insert B G).biUnion id = (A ∪ G.biUnion id) ∪ B := by
      ext x
      simp [Finset.mem_biUnion]
      constructor
      · intro hx
        rcases hx with hxA | hxB | hxG
        · exact Or.inl hxA
        · exact Or.inr (Or.inr hxB)
        · exact Or.inr (Or.inl hxG)
      · intro hx
        rcases hx with hxA | hxG | hxB
        · exact Or.inl hxA
        · exact Or.inr (Or.inr hxG)
        · exact Or.inr (Or.inl hxB)
    rw [hEq]
    exact hUnion

/-- A finite nonempty union-closed family has a maximum member: the union of
all its members. -/
theorem hasMaximum_familyUnion_of_nonempty {F : Finset (Finset α)}
    (hF : IsUnionClosed F) (hNonempty : F.Nonempty) :
    HasMaximum F (familyUnion F) := by
  rcases hNonempty with ⟨A, hA⟩
  refine ⟨?_, ?_⟩
  · have hMem : A ∪ F.biUnion id ∈ F :=
      union_biUnion_mem_of_subset (F := F) (G := F) (A := A) hF (by intro B hB; exact hB) hA
    have hEq : A ∪ F.biUnion id = familyUnion F := by
      apply Finset.Subset.antisymm
      · intro x hx
        rcases (by simpa using hx : x ∈ A ∨ x ∈ F.biUnion id) with hxA | hxU
        · rw [mem_familyUnion]
          exact ⟨A, hA, hxA⟩
        · simpa [familyUnion] using hxU
      · intro x hx
        have hxU : x ∈ F.biUnion id := by
          simpa [familyUnion] using hx
        simp [hxU]
    simpa [hEq] using hMem
  · intro B hB
    exact subset_familyUnion_of_mem hB

/-- Bottom-fiber propagation, in its minimal set-theoretic form.

If `M` is maximum in a fiber `G` and the union of a bottom-fiber set `A` with
`M` is still in `G`, then every element of `A` is already in `M`. -/
theorem subset_maximum_of_union_mem {G : Finset (Finset α)} {A M : Finset α}
    (hM : HasMaximum G M) (hUnion : A ∪ M ∈ G) :
    A ⊆ M := by
  intro x hxA
  have hSub : A ∪ M ⊆ M := hM.subset hUnion
  exact hSub (by simp [hxA])

/-- Elementwise form of bottom-fiber propagation. -/
theorem mem_maximum_of_mem_of_union_mem {G : Finset (Finset α)} {A M : Finset α}
    {x : α} (hM : HasMaximum G M) (hxA : x ∈ A) (hUnion : A ∪ M ∈ G) :
    x ∈ M :=
  subset_maximum_of_union_mem hM hUnion hxA

/-- Horn-style propagation: if every member of an output family contains `x`,
then whenever `A ∪ B` lies in that family, at least one of `A` or `B`
contains `x`.  This is the set-theoretic core of the propagation certificate
used in the research note. -/
theorem mem_left_or_mem_right_of_union_mem_all {G : Finset (Finset α)}
    {A B : Finset α} {x : α}
    (hAll : ∀ C ∈ G, x ∈ C) (hUnion : A ∪ B ∈ G) :
    x ∈ A ∨ x ∈ B := by
  have hxUnion : x ∈ A ∪ B := hAll (A ∪ B) hUnion
  simpa using hxUnion

/-- If every member of an output family contains `x`, and `A ∪ B` lies in that
family while `A` omits `x`, then `B` must contain `x`. -/
theorem mem_right_of_union_mem_all_of_not_mem_left {G : Finset (Finset α)}
    {A B : Finset α} {x : α}
    (hAll : ∀ C ∈ G, x ∈ C) (hUnion : A ∪ B ∈ G) (hxA : x ∉ A) :
    x ∈ B := by
  rcases mem_left_or_mem_right_of_union_mem_all hAll hUnion with hxA' | hxB
  · exact False.elim (hxA hxA')
  · exact hxB

/-- Symmetric form of `mem_right_of_union_mem_all_of_not_mem_left`. -/
theorem mem_left_of_union_mem_all_of_not_mem_right {G : Finset (Finset α)}
    {A B : Finset α} {x : α}
    (hAll : ∀ C ∈ G, x ∈ C) (hUnion : A ∪ B ∈ G) (hxB : x ∉ B) :
    x ∈ A := by
  rcases mem_left_or_mem_right_of_union_mem_all hAll hUnion with hxA | hxB'
  · exact hxA
  · exact False.elim (hxB hxB')

end Frankl
