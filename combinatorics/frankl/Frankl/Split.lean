import Frankl.Basic
import Mathlib.Tactic

/-!
# Split Families

Reference: `combinatorics/frankl/research/checklist.md`

For a coordinate `x`, split a family into the members omitting `x` and the
members containing `x`.  Frankl's half-bound for `x` is equivalent to the
right side of this split being at least as large as the left side.
-/

set_option autoImplicit false

namespace Frankl

variable {α : Type*} [DecidableEq α]

/-- The left side of the coordinate split: member-sets omitting `x`. -/
def leftSplit (x : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  nonmemberSubfamily x F

/-- The right side of the coordinate split: member-sets containing `x`. -/
def rightSplit (x : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  memberSubfamily x F

theorem mem_leftSplit {F : Finset (Finset α)} {A : Finset α} {x : α} :
    A ∈ leftSplit x F ↔ A ∈ F ∧ x ∉ A := by
  simp [leftSplit, mem_nonmemberSubfamily]

theorem mem_rightSplit {F : Finset (Finset α)} {A : Finset α} {x : α} :
    A ∈ rightSplit x F ↔ A ∈ F ∧ x ∈ A := by
  simp [rightSplit, mem_memberSubfamily]

theorem rightSplit_card_eq_memberCount (x : α) (F : Finset (Finset α)) :
    (rightSplit x F).card = memberCount x F := by
  rfl

/-- The split into sets containing and omitting `x` partitions the family. -/
theorem rightSplit_card_add_leftSplit_card (x : α) (F : Finset (Finset α)) :
    (rightSplit x F).card + (leftSplit x F).card = F.card := by
  simpa [rightSplit, leftSplit, memberSubfamily, nonmemberSubfamily] using
    (Finset.card_filter_add_card_filter_not
      (s := F) (p := fun A : Finset α => x ∈ A))

theorem leftSplit_card_add_rightSplit_card (x : α) (F : Finset (Finset α)) :
    (leftSplit x F).card + (rightSplit x F).card = F.card := by
  rw [Nat.add_comm]
  exact rightSplit_card_add_leftSplit_card x F

/-- The Frankl counting inequality for a fixed coordinate is equivalent to the
omitting side of the split having size at most the containing side. -/
theorem card_le_twice_rightSplit_iff (x : α) (F : Finset (Finset α)) :
    F.card ≤ 2 * (rightSplit x F).card ↔
      (leftSplit x F).card ≤ (rightSplit x F).card := by
  have hsplit := rightSplit_card_add_leftSplit_card x F
  constructor
  · intro h
    omega
  · intro h
    omega

/-- A coordinate is a Frankl element exactly when it appears somewhere and the
right side of its split is at least as large as the left side. -/
theorem isFranklElement_iff_leftSplit_card_le_rightSplit {F : Finset (Finset α)}
    {x : α} :
    IsFranklElement x F ↔
      x ∈ familyUnion F ∧ (leftSplit x F).card ≤ (rightSplit x F).card := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    exact (card_le_twice_rightSplit_iff x F).mp (by
      simpa [rightSplit, memberCount] using h.2)
  · intro h
    refine ⟨h.1, ?_⟩
    exact (by
      have hcount := (card_le_twice_rightSplit_iff x F).mpr h.2
      simpa [rightSplit, memberCount] using hcount)

end Frankl
