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

/-- The two-element (doubleton) case of Frankl's conjecture.  If a union-closed
family contains the pair `{a, b}` with `a ≠ b`, then `a` or `b` lies in at least
half of the member-sets.

Partition `F` by the membership pattern of `a` then `b` into four blocks with
cardinalities `n₀₀, n₀₁, n₁₀, n₁₁` (subscripts record membership of `a` then
`b`).  The map `A ↦ insert a (insert b A)` injects the `(a∉, b∉)` block into the
`(a∈, b∈)` block — it lands in `F` because `{a,b} ∈ F` and `F` is union-closed —
so `n₀₀ ≤ n₁₁`.  If neither `a` nor `b` were a Frankl element we would have
`n₁₀ + n₁₁ < n₀₀ + n₀₁` and `n₀₁ + n₁₁ < n₀₀ + n₁₀`; summing forces `n₁₁ < n₀₀`,
contradicting `n₀₀ ≤ n₁₁`.

This is a classical small-case result: Frankl's conjecture holds for any family
containing a set of size at most two (see the Bruhn–Schaudt survey "The journey
of the union-closed sets conjecture", Graphs and Combinatorics 31 (2015)). -/
theorem isFranklElement_left_or_right_of_pair_mem {F : Finset (Finset α)}
    {a b : α} (hF : IsUnionClosed F) (hab : a ≠ b)
    (hpair : ({a, b} : Finset α) ∈ F) :
    IsFranklElement a F ∨ IsFranklElement b F := by
  classical
  have haU : a ∈ familyUnion F := by
    rw [mem_familyUnion]; exact ⟨{a, b}, hpair, by simp⟩
  have hbU : b ∈ familyUnion F := by
    rw [mem_familyUnion]; exact ⟨{a, b}, hpair, by simp⟩
  -- The four membership blocks, with predicates written `a`-first then `b`.
  set F00 := F.filter (fun A => ¬ a ∈ A ∧ ¬ b ∈ A) with hF00
  set F01 := F.filter (fun A => ¬ a ∈ A ∧ b ∈ A) with hF01
  set F10 := F.filter (fun A => a ∈ A ∧ ¬ b ∈ A) with hF10
  set F11 := F.filter (fun A => a ∈ A ∧ b ∈ A) with hF11
  -- `A ↦ insert a (insert b A)` injects the `(a∉,b∉)` block into the `(a∈,b∈)` block.
  have hinj : F00.card ≤ F11.card := by
    refine Finset.card_le_card_of_injOn (fun A => insert a (insert b A)) ?maps ?inj
    · intro A hA
      rw [Finset.mem_coe, hF00, Finset.mem_filter] at hA
      obtain ⟨hAF, haA, hbA⟩ := hA
      simp only [Finset.mem_coe, hF11, Finset.mem_filter]
      refine ⟨?_, by simp, by simp⟩
      have hrw : insert a (insert b A) = ({a, b} : Finset α) ∪ A := by
        ext y; simp [Finset.mem_insert]
      rw [hrw]; exact hF _ hpair _ hAF
    · intro A hA B hB hEq
      rw [Finset.mem_coe, hF00, Finset.mem_filter] at hA hB
      obtain ⟨_, haA, hbA⟩ := hA
      obtain ⟨_, haB, hbB⟩ := hB
      ext y
      by_cases hya : y = a
      · subst hya; simp [haA, haB]
      · by_cases hyb : y = b
        · subst hyb; simp [hbA, hbB]
        · have hy := congrArg (fun s : Finset α => y ∈ s) hEq
          simpa [Finset.mem_insert, hya, hyb] using hy
  -- Counting identities, then `omega` closes the arithmetic.
  have hMa : memberCount a F = F11.card + F10.card := by
    unfold memberCount memberSubfamily
    rw [← Finset.card_filter_add_card_filter_not
          (s := F.filter (fun A => a ∈ A)) (fun A => b ∈ A),
        hF11, hF10, Finset.filter_filter, Finset.filter_filter]
  have hMb : memberCount b F = F11.card + F01.card := by
    unfold memberCount memberSubfamily
    rw [← Finset.card_filter_add_card_filter_not
          (s := F.filter (fun A => b ∈ A)) (fun A => a ∈ A),
        Finset.filter_filter, Finset.filter_filter, hF11, hF01]
    congr 1 <;> exact congrArg Finset.card (Finset.filter_congr fun A _ => and_comm)
  have hFc : F.card = F11.card + F10.card + (F01.card + F00.card) := by
    have e1 : F.card =
        (F.filter (fun A => a ∈ A)).card + (F.filter (fun A => ¬ a ∈ A)).card :=
      (Finset.card_filter_add_card_filter_not (s := F) (fun A => a ∈ A)).symm
    have e2 : (F.filter (fun A => a ∈ A)).card = F11.card + F10.card := by
      rw [← Finset.card_filter_add_card_filter_not
            (s := F.filter (fun A => a ∈ A)) (fun A => b ∈ A),
          hF11, hF10, Finset.filter_filter, Finset.filter_filter]
    have e3 : (F.filter (fun A => ¬ a ∈ A)).card = F01.card + F00.card := by
      rw [← Finset.card_filter_add_card_filter_not
            (s := F.filter (fun A => ¬ a ∈ A)) (fun A => b ∈ A),
          hF01, hF00, Finset.filter_filter, Finset.filter_filter]
    rw [e1, e2, e3]
  have key : F.card ≤ 2 * memberCount a F ∨ F.card ≤ 2 * memberCount b F := by
    omega
  rcases key with h | h
  · exact Or.inl ⟨haU, h⟩
  · exact Or.inr ⟨hbU, h⟩

/-- The two-element case packaged as `FranklConjectureFor`. -/
theorem franklConjectureFor_of_pair_mem {F : Finset (Finset α)} {a b : α}
    (hab : a ≠ b) (hpair : ({a, b} : Finset α) ∈ F) :
    FranklConjectureFor F := by
  intro hF _hNonempty
  rcases isFranklElement_left_or_right_of_pair_mem hF hab hpair with h | h
  · exact ⟨a, h⟩
  · exact ⟨b, h⟩

end Frankl
