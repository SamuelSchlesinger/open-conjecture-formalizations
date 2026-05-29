import Frankl.Fiber
import Mathlib.Tactic

/-!
# The coatom lemma for balanced union-closed families

Reference: `combinatorics/frankl/research/frankl_tight_boolean.md`

This file formalizes a proved layer of the `tight ⟺ Boolean` extremal
characterization (the "crux B" reduction).  Working on the set side, the
relevant condition is **every-half**: every ground element lies in exactly half
the member-sets of a union-closed family `F` (`2 * memberCount x F = |F|`).  Such
families are conjectured to be Boolean fields of sets; the first layer of that
statement is provable outright.

> **Coatom lemma.**  If `F` is union-closed, every-half, and *twin-free*
> (distinct ground elements have distinct member-subfamilies), then for every
> ground element `i` the coatom `(familyUnion F).erase i` is itself a member of
> `F`.

The mathematical content: twin-free makes the member-subfamilies
`U_i := memberSubfamily i F` pairwise distinct, every-half makes them all the
same size `|F|/2`; equal-size distinct finite sets are incomparable, so for any
`i ≠ j` some member contains `j` but not `i`.  The union `N_i` of all members
avoiding `i` is therefore a member (union-closure) that omits `i` yet contains
every other ground element — i.e. exactly the coatom `U ∖ {i}`.

In closure-system language (taking complements) this is the dual refinement of
the already-proved "all-half ⟹ join-irreducibles are atoms": *all-half forces
the atoms to be the points and all of them to be present*.  The deeper claim
"every-half ⟹ the full power set" needs a second-moment (degree-2) balance that
every-half does not by itself supply; see the research note.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Frankl

variable {α : Type*} [DecidableEq α]

/-- A family is **every-half** when every ground element lies in exactly half of
the member-sets: `2 * memberCount x F = |F|` for all `x` in the family union. -/
def IsEveryHalf (F : Finset (Finset α)) : Prop :=
  ∀ x ∈ familyUnion F, 2 * memberCount x F = F.card

/-- A family is **twin-free** when distinct ground elements are distinguished by
the member-sets containing them (no two elements lie in exactly the same
members). -/
def IsTwinFree (F : Finset (Finset α)) : Prop :=
  ∀ x ∈ familyUnion F, ∀ y ∈ familyUnion F,
    memberSubfamily x F = memberSubfamily y F → x = y

/-- The union of any nonempty subfamily of a union-closed family is a member. -/
theorem biUnion_id_mem_of_nonempty_subset {F G : Finset (Finset α)}
    (hF : IsUnionClosed F) (hG : G ⊆ F) (hGne : G.Nonempty) :
    G.biUnion id ∈ F := by
  obtain ⟨A, hAG⟩ := hGne
  have hmem : A ∪ G.biUnion id ∈ F :=
    union_biUnion_mem_of_subset hF hG (hG hAG)
  have hAsub : A ⊆ G.biUnion id :=
    show A ⊆ G.biUnion id from Finset.subset_biUnion_of_mem id hAG
  rwa [Finset.union_eq_right.mpr hAsub] at hmem

/-- **Incomparability.**  In an every-half, twin-free family, for any two
distinct ground elements `i ≠ j` there is a member containing `j` but not `i`.
(The two member-subfamilies are distinct and of equal size `|F|/2`, hence
incomparable.) -/
theorem exists_mem_of_everyHalf_twinFree {F : Finset (Finset α)}
    (hHalf : IsEveryHalf F) (hTwin : IsTwinFree F)
    {i j : α} (hi : i ∈ familyUnion F) (hj : j ∈ familyUnion F) (hij : i ≠ j) :
    ∃ A ∈ F, j ∈ A ∧ i ∉ A := by
  have hci : 2 * memberCount i F = F.card := hHalf i hi
  have hcj : 2 * memberCount j F = F.card := hHalf j hj
  have hcard_eq : memberCount i F = memberCount j F := by omega
  by_contra hcon
  push_neg at hcon
  have hsub : memberSubfamily j F ⊆ memberSubfamily i F := by
    intro A hA
    rw [mem_memberSubfamily] at hA ⊢
    exact ⟨hA.1, hcon A hA.1 hA.2⟩
  have hle : (memberSubfamily i F).card ≤ (memberSubfamily j F).card := by
    show memberCount i F ≤ memberCount j F
    omega
  have heq : memberSubfamily j F = memberSubfamily i F :=
    Finset.eq_of_subset_of_card_le hsub hle
  exact hij (hTwin j hj i hi heq).symm

/-- **Coatom lemma.**  A union-closed, every-half, twin-free family contains every
coatom `(familyUnion F).erase i`. -/
theorem coatom_mem_of_everyHalf_twinFree {F : Finset (Finset α)}
    (hF : IsUnionClosed F) (hHalf : IsEveryHalf F) (hTwin : IsTwinFree F)
    {i : α} (hi : i ∈ familyUnion F) :
    (familyUnion F).erase i ∈ F := by
  set N := (nonmemberSubfamily i F).biUnion id with hN
  have hci : 2 * memberCount i F = F.card := hHalf i hi
  have hmc_pos : 0 < memberCount i F := by
    obtain ⟨A, hA, hiA⟩ := mem_familyUnion.mp hi
    exact memberCount_pos_of_mem hA hiA
  have hpart : memberCount i F + (nonmemberSubfamily i F).card = F.card := by
    unfold memberCount memberSubfamily nonmemberSubfamily
    exact Finset.card_filter_add_card_filter_not (s := F) (fun A => i ∈ A)
  have hne : (nonmemberSubfamily i F).Nonempty := by
    rw [← Finset.card_pos]; omega
  have hsubF : nonmemberSubfamily i F ⊆ F := by
    intro A hA; exact (mem_nonmemberSubfamily.mp hA).1
  have hNmem : N ∈ F := biUnion_id_mem_of_nonempty_subset hF hsubF hne
  have hiN : i ∉ N := by
    rw [hN, Finset.mem_biUnion]
    rintro ⟨A, hA, hiA⟩
    exact (mem_nonmemberSubfamily.mp hA).2 hiA
  have hNeq : N = (familyUnion F).erase i := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact hiN hx
      · rw [hN, Finset.mem_biUnion] at hx
        obtain ⟨A, hA, hxA⟩ := hx
        exact subset_familyUnion_of_mem (mem_nonmemberSubfamily.mp hA).1 hxA
    · intro x hx
      rw [Finset.mem_erase] at hx
      obtain ⟨hxi, hxU⟩ := hx
      obtain ⟨A, hA, hxA, hiA⟩ :=
        exists_mem_of_everyHalf_twinFree hHalf hTwin hi hxU (Ne.symm hxi)
      rw [hN, Finset.mem_biUnion]
      exact ⟨A, by rw [mem_nonmemberSubfamily]; exact ⟨hA, hiA⟩, hxA⟩
  rw [← hNeq]; exact hNmem

end Frankl
