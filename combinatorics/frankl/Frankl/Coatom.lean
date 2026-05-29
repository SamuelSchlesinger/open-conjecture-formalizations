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

/-- A family is **intersection-closed** when the intersection of any two
member-sets is again a member-set. -/
def IsInterClosed (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F

/-- With all coatoms present (the coatom lemma) and intersection-closure, every
subset `U ∖ T` of the ground set is reached: peel `T` one element at a time,
intersecting with the corresponding coatom. -/
theorem sdiff_mem_of_everyHalf_twinFree_interClosed {F : Finset (Finset α)}
    (hF : IsUnionClosed F) (hInt : IsInterClosed F)
    (hHalf : IsEveryHalf F) (hTwin : IsTwinFree F) (hne : F.Nonempty) :
    ∀ T, T ⊆ familyUnion F → familyUnion F \ T ∈ F := by
  intro T
  induction T using Finset.induction with
  | empty =>
      intro _
      have hU : familyUnion F ∈ F := by
        have h := biUnion_id_mem_of_nonempty_subset hF (Finset.Subset.refl F) hne
        simpa [familyUnion] using h
      simpa using hU
  | insert i T' hiT' ih =>
      intro hsub
      have hiU : i ∈ familyUnion F := hsub (Finset.mem_insert_self i T')
      have hT'sub : T' ⊆ familyUnion F :=
        fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hco : (familyUnion F).erase i ∈ F :=
        coatom_mem_of_everyHalf_twinFree hF hHalf hTwin hiU
      have hEq : familyUnion F \ insert i T'
          = (familyUnion F \ T') ∩ (familyUnion F).erase i := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter,
          Finset.mem_erase]
        tauto
      rw [hEq]
      exact hInt _ (ih hT'sub) _ hco

/-- **Field-of-sets characterization.**  A union-closed *and* intersection-closed
(`= field of sets`), every-half, twin-free family is the full power set of its
ground set.

This is the provable core of the "crux B" reduction in the `tight ⟺ Boolean`
characterization (`research/frankl_tight_boolean.md`): the coatom lemma supplies
all coatoms, and intersection-closure then generates every subset.  Dropping the
intersection-closure hypothesis is exactly the open, conjecture-equivalent
residual (it would require a second-moment balance that every-half alone does
not provide). -/
theorem eq_powerset_of_everyHalf_twinFree_interClosed {F : Finset (Finset α)}
    (hF : IsUnionClosed F) (hInt : IsInterClosed F)
    (hHalf : IsEveryHalf F) (hTwin : IsTwinFree F) (hne : F.Nonempty) :
    F = (familyUnion F).powerset := by
  apply Finset.Subset.antisymm
  · intro A hA
    rw [Finset.mem_powerset]
    exact subset_familyUnion_of_mem hA
  · intro S hS
    rw [Finset.mem_powerset] at hS
    have hsdiff :
        familyUnion F \ (familyUnion F \ S) = S := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨hxU, hx⟩
        by_contra hxS
        exact hx ⟨hxU, hxS⟩
      · intro hxS
        exact ⟨hS hxS, fun h => h.2 hxS⟩
    rw [← hsdiff]
    exact sdiff_mem_of_everyHalf_twinFree_interClosed hF hInt hHalf hTwin hne
      _ Finset.sdiff_subset

/-! ### The power set realizes every hypothesis (sharpness)

The full power set `V.powerset` is union-closed, intersection-closed, twin-free,
and every-half — so the characterization above is exact, and Frankl's `½` bound
is achieved with *equality at every element* by the power set. -/

theorem familyUnion_powerset (V : Finset α) : familyUnion V.powerset = V := by
  ext x
  rw [mem_familyUnion]
  constructor
  · rintro ⟨A, hA, hxA⟩
    exact (Finset.mem_powerset.mp hA) hxA
  · intro hx
    exact ⟨V, Finset.mem_powerset.mpr (Finset.Subset.refl V), hx⟩

theorem isUnionClosed_powerset (V : Finset α) : IsUnionClosed V.powerset := by
  intro A hA B hB
  rw [Finset.mem_powerset] at hA hB ⊢
  exact Finset.union_subset hA hB

theorem isInterClosed_powerset (V : Finset α) : IsInterClosed V.powerset := by
  intro A hA B hB
  rw [Finset.mem_powerset] at hA ⊢
  exact Finset.inter_subset_left.trans hA

theorem isTwinFree_powerset (V : Finset α) : IsTwinFree V.powerset := by
  intro x hx y _ hxy
  rw [familyUnion_powerset] at hx
  have hxmem : ({x} : Finset α) ∈ memberSubfamily x V.powerset := by
    rw [mem_memberSubfamily, Finset.mem_powerset]
    exact ⟨Finset.singleton_subset_iff.mpr hx, Finset.mem_singleton_self x⟩
  rw [hxy, mem_memberSubfamily] at hxmem
  exact (Finset.mem_singleton.mp hxmem.2).symm

theorem isEveryHalf_powerset (V : Finset α) : IsEveryHalf V.powerset := by
  intro x hx
  rw [familyUnion_powerset] at hx
  have hfilter_not :
      V.powerset.filter (fun A => x ∉ A) = (V.erase x).powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
  have hsum : memberCount x V.powerset + (V.erase x).powerset.card
      = V.powerset.card := by
    have h := Finset.card_filter_add_card_filter_not (s := V.powerset)
      (fun A => x ∈ A)
    rw [hfilter_not] at h
    simpa [memberCount, memberSubfamily] using h
  rw [Finset.card_powerset, Finset.card_powerset, Finset.card_erase_of_mem hx]
    at hsum
  rw [Finset.card_powerset]
  have hpos : 1 ≤ V.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hpow : 2 ^ V.card = 2 ^ (V.card - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hpos]
    rw [pow_succ]
  omega

/-- **Every-half field of sets ⟺ power set.**  A nonempty family is a twin-free
field of sets (union- and intersection-closed) with every element in exactly
half the members **iff** it is the full power set of its ground set.  The forward
direction is the coatom-lemma payoff; the reverse shows the power set realizes
all the hypotheses, so Frankl's `½` bound is sharp (equality everywhere). -/
theorem everyHalf_field_iff_powerset {F : Finset (Finset α)} (hne : F.Nonempty) :
    (IsUnionClosed F ∧ IsInterClosed F ∧ IsEveryHalf F ∧ IsTwinFree F)
      ↔ F = (familyUnion F).powerset := by
  constructor
  · rintro ⟨hU, hI, hH, hT⟩
    exact eq_powerset_of_everyHalf_twinFree_interClosed hU hI hH hT hne
  · intro hEq
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hEq]; exact isUnionClosed_powerset _
    · rw [hEq]; exact isInterClosed_powerset _
    · rw [hEq]; exact isEveryHalf_powerset _
    · rw [hEq]; exact isTwinFree_powerset _

end Frankl
