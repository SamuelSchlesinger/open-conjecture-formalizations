import Frankl.Basic
import Mathlib.Tactic

/-!
# Twin-Deletion Reduction for Frankl's Conjecture

Two ground elements `i, j` are *twins* in a family `F` when they belong to
exactly the same member-sets: `∀ A ∈ F, (i ∈ A ↔ j ∈ A)`.  When `F` has a pair
of twins, one of them is redundant: deleting the element `j` from every
member-set produces a strictly "smaller" family `F' = {A.erase j : A ∈ F}` that
satisfies Frankl's conjecture if and only if the original one does.

This file proves the *reduction* direction needed to peel twins away: if the
deleted family `F'` satisfies the conjecture, then so does `F`.  Iterating this
reduces Frankl's conjecture to *separating* (twin-free) families, in which no
two ground elements have identical membership patterns.

The key observation is that the deletion map `A ↦ A.erase j` is injective on a
family with the twin property: two member-sets that agree off `j` must also
agree on `j`, because membership of `j` is determined by membership of its twin
`i ≠ j`, which is recorded in `A.erase j`.  Injectivity makes the deletion map a
cardinality-preserving bijection onto `F'`, and it also preserves the per-element
counts for every surviving element, so a Frankl witness for `F'` transports back
to a Frankl witness for `F`.

Reference: https://doi.org/10.1016/0097-3165(92)90068-6
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Frankl

variable {α : Type*} [DecidableEq α]

/-- Deleting a fixed element `j` from every member-set of a union-closed family
yields a union-closed family.  This is step 1 of the twin-deletion reduction and
is useful on its own: `(A ∪ B).erase j = A.erase j ∪ B.erase j`, so the image of
a union is the union of the images. -/
theorem isUnionClosed_image_erase {F : Finset (Finset α)} (hF : IsUnionClosed F)
    (j : α) :
    IsUnionClosed (F.image (fun A => A.erase j)) := by
  intro A' hA' B' hB'
  rw [Finset.mem_image] at hA' hB'
  obtain ⟨A, hA, rfl⟩ := hA'
  obtain ⟨B, hB, rfl⟩ := hB'
  rw [Finset.mem_image]
  refine ⟨A ∪ B, hF A hA B hB, ?_⟩
  rw [Finset.erase_union_distrib]

/-- The deletion map `A ↦ A.erase j` is injective on a family with the twin
property.  If `A, B ∈ F` satisfy `A.erase j = B.erase j` then they agree on every
element other than `j`; and they agree on `j` too, because `j ∈ A ↔ i ∈ A` (twin,
using `i ≠ j`) and `i ∈ A ↔ i ∈ A.erase j` is recorded by the erased set. -/
theorem injOn_erase_of_twin {F : Finset (Finset α)} {i j : α} (hij : i ≠ j)
    (htwin : ∀ A ∈ F, (i ∈ A ↔ j ∈ A)) :
    Set.InjOn (fun A => A.erase j) (F : Set (Finset α)) := by
  intro A hA B hB hEq
  simp only [Finset.mem_coe] at hA hB
  simp only at hEq
  -- `hEq : A.erase j = B.erase j`; turn it into a membership equivalence.
  have hmem : ∀ y, y ∈ A.erase j ↔ y ∈ B.erase j := fun y => by rw [hEq]
  -- Determine membership of `j` through its twin `i ≠ j`.
  have hi : i ∈ A.erase j ↔ i ∈ B.erase j := hmem i
  rw [Finset.mem_erase, Finset.mem_erase] at hi
  have hjAB : j ∈ A ↔ j ∈ B := by
    have htA : i ∈ A ↔ j ∈ A := htwin A hA
    have htB : i ∈ B ↔ j ∈ B := htwin B hB
    tauto
  apply Finset.ext
  intro y
  by_cases hyj : y = j
  · subst hyj; exact hjAB
  · have hy := hmem y
    rw [Finset.mem_erase, Finset.mem_erase] at hy
    tauto

/-- The deletion map preserves the family cardinality on a twin family, because
it is injective there. -/
theorem card_image_erase_of_twin {F : Finset (Finset α)} {i j : α} (hij : i ≠ j)
    (htwin : ∀ A ∈ F, (i ∈ A ↔ j ∈ A)) :
    (F.image (fun A => A.erase j)).card = F.card :=
  Finset.card_image_of_injOn (injOn_erase_of_twin hij htwin)

/-- For any element `x ≠ j`, deletion of `j` carries the member-subfamily of `x`
in `F` exactly onto the member-subfamily of `x` in `F'`.  Since `x ≠ j`,
membership of `x` is unaffected by erasing `j`. -/
theorem memberSubfamily_image_erase {F : Finset (Finset α)} {x j : α}
    (hxj : x ≠ j) :
    memberSubfamily x (F.image (fun A => A.erase j))
      = (memberSubfamily x F).image (fun A => A.erase j) := by
  ext A'
  simp only [mem_memberSubfamily, Finset.mem_image]
  constructor
  · rintro ⟨⟨A, hA, rfl⟩, hxA'⟩
    rw [Finset.mem_erase] at hxA'
    exact ⟨A, ⟨hA, hxA'.2⟩, rfl⟩
  · rintro ⟨A, ⟨hA, hxA⟩, rfl⟩
    refine ⟨⟨A, hA, rfl⟩, ?_⟩
    rw [Finset.mem_erase]
    exact ⟨hxj, hxA⟩

/-- For any element `x ≠ j`, the deletion map preserves the count of member-sets
containing `x`. -/
theorem memberCount_image_erase_of_twin {F : Finset (Finset α)} {i j : α}
    (hij : i ≠ j) (htwin : ∀ A ∈ F, (i ∈ A ↔ j ∈ A)) {x : α} (hxj : x ≠ j) :
    memberCount x (F.image (fun A => A.erase j)) = memberCount x F := by
  unfold memberCount
  rw [memberSubfamily_image_erase hxj]
  refine Finset.card_image_of_injOn ?_
  refine Set.InjOn.mono ?_ (injOn_erase_of_twin hij htwin)
  intro A hA
  rw [Finset.mem_coe, mem_memberSubfamily] at hA
  exact hA.1

/-- Deleting `j` from every member-set of a family with a nonempty member yields
a family with a nonempty member.  If a nonempty `A ∈ F` already omits `j`, then
`A.erase j = A` is nonempty; if `j ∈ A` then the twin `i ∈ A` and `i ≠ j`, so
`i ∈ A.erase j`. -/
theorem hasNonemptyMember_image_erase_of_twin {F : Finset (Finset α)} {i j : α}
    (hij : i ≠ j) (htwin : ∀ A ∈ F, (i ∈ A ↔ j ∈ A))
    (hNE : HasNonemptyMember F) :
    HasNonemptyMember (F.image (fun A => A.erase j)) := by
  obtain ⟨A, hA, hANE⟩ := hNE
  refine ⟨A.erase j, Finset.mem_image_of_mem _ hA, ?_⟩
  by_cases hjA : j ∈ A
  · -- `j ∈ A`, so its twin `i ∈ A` survives the erasure.
    have hiA : i ∈ A := (htwin A hA).mpr hjA
    exact ⟨i, by rw [Finset.mem_erase]; exact ⟨hij, hiA⟩⟩
  · -- `j ∉ A`, so `A.erase j = A` stays nonempty.
    rw [Finset.erase_eq_of_notMem hjA]
    exact hANE

/-- Every member-set of the deleted family `F'` omits `j`, hence `j` is not in
the family-union of `F'`. -/
theorem notMem_familyUnion_image_erase {F : Finset (Finset α)} {j : α} :
    j ∉ familyUnion (F.image (fun A => A.erase j)) := by
  rw [mem_familyUnion]
  rintro ⟨A', hA', hjA'⟩
  rw [Finset.mem_image] at hA'
  obtain ⟨A, _, rfl⟩ := hA'
  exact (Finset.notMem_erase j A) hjA'

/-- **Twin-deletion reduction.**  If `i ≠ j` are twins in `F` (they lie in the
same member-sets), then Frankl's conjecture for `F` follows from Frankl's
conjecture for the deleted family `F' = {A.erase j : A ∈ F}`.

The Frankl witness `x` produced for `F'` necessarily differs from `j` (which
appears in no member of `F'`), and the deletion map preserves both the family
size and the count of `x`, so `x` is also a Frankl witness for `F`. -/
theorem franklConjectureFor_of_erase_twin {F : Finset (Finset α)} {i j : α}
    (hij : i ≠ j) (htwin : ∀ A ∈ F, (i ∈ A ↔ j ∈ A))
    (h' : FranklConjectureFor (F.image (fun A => A.erase j))) :
    FranklConjectureFor F := by
  intro hUC hNE
  set F' := F.image (fun A => A.erase j) with hF'
  -- Transport the hypotheses to `F'` and apply the conjecture there.
  have hUC' : IsUnionClosed F' := isUnionClosed_image_erase hUC j
  have hNE' : HasNonemptyMember F' :=
    hasNonemptyMember_image_erase_of_twin hij htwin hNE
  obtain ⟨x, hxU, hxCount⟩ := h' hUC' hNE'
  -- The witness `x` avoids `j`, since `j` lies in no member of `F'`.
  have hxj : x ≠ j := by
    rintro rfl
    exact notMem_familyUnion_image_erase hxU
  refine ⟨x, ?_, ?_⟩
  · -- `x ∈ familyUnion F'` lifts to `x ∈ familyUnion F`.
    rw [mem_familyUnion] at hxU ⊢
    obtain ⟨A', hA', hxA'⟩ := hxU
    rw [hF', Finset.mem_image] at hA'
    obtain ⟨A, hA, rfl⟩ := hA'
    exact ⟨A, hA, (Finset.mem_erase.mp hxA').2⟩
  · -- Cardinalities and counts are preserved, so the inequality transports.
    rw [← card_image_erase_of_twin hij htwin, ← hF',
      ← memberCount_image_erase_of_twin hij htwin hxj, ← hF']
    exact hxCount

end Frankl
