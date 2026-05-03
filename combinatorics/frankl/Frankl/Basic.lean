import Frankl.Defs
import Mathlib.Tactic

/-!
# Basic Lemmas for Frankl's Conjecture

Reference: https://arxiv.org/abs/1207.3604
-/

set_option autoImplicit false

namespace Frankl

variable {α : Type*} [DecidableEq α]

theorem mem_familyUnion {F : Finset (Finset α)} {x : α} :
    x ∈ familyUnion F ↔ ∃ A ∈ F, x ∈ A := by
  simp [familyUnion]

theorem subset_familyUnion_of_mem {F : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ F) :
    A ⊆ familyUnion F := by
  intro x hx
  rw [mem_familyUnion]
  exact ⟨A, hA, hx⟩

theorem mem_memberSubfamily {F : Finset (Finset α)} {A : Finset α} {x : α} :
    A ∈ memberSubfamily x F ↔ A ∈ F ∧ x ∈ A := by
  simp [memberSubfamily]

theorem mem_nonmemberSubfamily {F : Finset (Finset α)} {A : Finset α} {x : α} :
    A ∈ nonmemberSubfamily x F ↔ A ∈ F ∧ x ∉ A := by
  simp [nonmemberSubfamily]

theorem memberCount_le_card (F : Finset (Finset α)) (x : α) :
    memberCount x F ≤ F.card := by
  exact Finset.card_le_card (Finset.filter_subset _ F)

theorem memberCount_pos_of_mem {F : Finset (Finset α)} {A : Finset α} {x : α}
    (hA : A ∈ F) (hxA : x ∈ A) :
    0 < memberCount x F := by
  unfold memberCount
  exact Finset.card_pos.mpr ⟨A, by rw [mem_memberSubfamily]; exact ⟨hA, hxA⟩⟩

theorem isUnionClosed_empty : IsUnionClosed (∅ : Finset (Finset α)) := by
  intro A hA
  simp at hA

theorem isUnionClosed_singleton_empty :
    IsUnionClosed ({∅} : Finset (Finset α)) := by
  intro A hA B hB
  simp at hA hB ⊢
  exact ⟨hA, hB⟩

/-- If a union-closed family contains `{x}`, then adding `x` injects the sets
that omit `x` into the sets that contain `x`. -/
theorem nonmember_card_le_memberCount_of_singleton_mem {F : Finset (Finset α)}
    {x : α} (hF : IsUnionClosed F) (hxF : ({x} : Finset α) ∈ F) :
    (nonmemberSubfamily x F).card ≤ memberCount x F := by
  unfold memberCount
  refine Finset.card_le_card_of_injOn (fun A : Finset α => insert x A) ?maps ?inj
  · intro A hA
    change A ∈ nonmemberSubfamily x F at hA
    change insert x A ∈ memberSubfamily x F
    rw [mem_nonmemberSubfamily] at hA
    rw [mem_memberSubfamily]
    refine ⟨?_, by simp⟩
    have hUnion : ({x} : Finset α) ∪ A ∈ F := hF {x} hxF A hA.1
    have hInsertUnion : insert x A = ({x} : Finset α) ∪ A := by
      ext y
      simp
    rw [hInsertUnion]
    exact hUnion
  · intro A hA B hB hEq
    change A ∈ nonmemberSubfamily x F at hA
    change B ∈ nonmemberSubfamily x F at hB
    rw [mem_nonmemberSubfamily] at hA hB
    apply Finset.ext
    intro y
    by_cases hy : y = x
    · subst y
      simp [hA.2, hB.2]
    · have hEq' : insert x A = insert x B := by
        exact hEq
      have hmem : y ∈ insert x A ↔ y ∈ insert x B := by
        rw [hEq']
      simpa [Finset.mem_insert, hy] using hmem

/-- The singleton-containing case of Frankl's conjecture.  The injection
`A ↦ A ∪ {x}` pairs every member-set omitting `x` with a distinct member-set
containing `x`, so `x` appears in at least half the family. -/
theorem isFranklElement_of_singleton_mem {F : Finset (Finset α)} {x : α}
    (hF : IsUnionClosed F) (hxF : ({x} : Finset α) ∈ F) :
    IsFranklElement x F := by
  refine ⟨?_, ?_⟩
  · rw [mem_familyUnion]
    exact ⟨{x}, hxF, by simp⟩
  · have hle :=
      nonmember_card_le_memberCount_of_singleton_mem (F := F) (x := x) hF hxF
    have hsplit : memberCount x F + (nonmemberSubfamily x F).card = F.card := by
      simp [memberCount, memberSubfamily, nonmemberSubfamily,
        Finset.card_filter_add_card_filter_not]
    omega

theorem franklConjectureFor_of_singleton_mem {F : Finset (Finset α)} {x : α}
    (hxF : ({x} : Finset α) ∈ F) :
    FranklConjectureFor F := by
  intro hF _hNonempty
  exact ⟨x, isFranklElement_of_singleton_mem hF hxF⟩

end Frankl
