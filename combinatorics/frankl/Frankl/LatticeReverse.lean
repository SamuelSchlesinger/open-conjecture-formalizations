import Frankl.Lattice
import Mathlib.Tactic

/-!
# Reverse direction: the lattice conjecture implies the set conjecture

This file proves `FranklLattice → FranklConjecture`, completing Poonen's
equivalence (`franklConjecture_iff_franklLattice`).  Given a finite union-closed
family `F` (reduced to the case `∅ ∈ F`), the poset `(F, ⊆)` is a finite lattice
(join `= ∪`, meet `=` the largest member contained in the intersection).  A
meet-irreducible element `m` has a unique upper cover `m⁺`; picking `x ∈ m⁺ ∖ m`
makes `m` the largest `x`-free member, so the principal ideal `↓m` is exactly the
set of `x`-free members.  The dual lattice conjecture (`FranklLatticeMeet`) then
yields a meet-irreducible `m` with `2 |↓m| ≤ |F|`, i.e. an abundant element `x`.
-/

set_option autoImplicit false

namespace Frankl

open Finset

/-- In a finite lattice, a meet-irreducible element `m` has a *least* strict
upper bound `m⁺` (its unique upper cover): `m < m⁺` and every `a > m` satisfies
`m⁺ ≤ a`.  Proof: `m⁺` is the meet of all strict upper bounds; meet-irreducibility
(via `InfIrred.finset_inf_eq`) keeps `m⁺` strictly above `m`. -/
theorem InfIrred.exists_least_gt {L : Type*} [Lattice L] [Fintype L] {m : L}
    (hm : InfIrred m) :
    ∃ m' : L, m < m' ∧ ∀ a : L, m < a → m' ≤ a := by
  classical
  haveI : Nonempty L := ⟨m⟩
  haveI : OrderTop L := Fintype.toOrderTop L
  obtain ⟨b, hb⟩ := not_isMax_iff.mp hm.1
  set U : Finset L := univ.filter (fun a => m < a) with hU
  have hUne : U.Nonempty := ⟨b, mem_filter.mpr ⟨mem_univ _, hb⟩⟩
  have hle : m ≤ U.inf' hUne id :=
    Finset.le_inf' hUne id (fun a ha => (mem_filter.mp ha).2.le)
  refine ⟨U.inf' hUne id, ?_, fun a ha => Finset.inf'_le id (mem_filter.mpr ⟨mem_univ _, ha⟩)⟩
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hinf : U.inf id = m := by rw [← Finset.inf'_eq_inf hUne id]; exact h.symm
    obtain ⟨u, hu, hum⟩ := hm.finset_inf_eq hinf
    exact absurd hum.symm (mem_filter.mp hu).2.ne

variable {α : Type} [DecidableEq α]

/-- The join (`Finset.sup`) of any subfamily of a union-closed family containing
`∅` stays in the family. -/
theorem sup_id_mem {F : Finset (Finset α)} (hF : IsUnionClosed F) (h0 : ∅ ∈ F)
    {T : Finset (Finset α)} (hT : T ⊆ F) : T.sup id ∈ F := by
  classical
  induction T using Finset.induction with
  | empty => simpa using h0
  | insert a s ha ih =>
      rw [Finset.sup_insert]
      have haF : a ∈ F := hT (mem_insert_self a s)
      have hsF : s.sup id ∈ F := ih (fun x hx => hT (mem_insert_of_mem hx))
      have : (id a) ∪ s.sup id ∈ F := hF _ haF _ hsF
      simpa [Finset.sup_eq_union] using this

/-- The lattice structure on a union-closed family `F` (with `∅ ∈ F`): join is
union, meet is the largest member contained in the intersection. -/
def ucLattice {F : Finset (Finset α)} (hF : IsUnionClosed F) (h0 : ∅ ∈ F) :
    Lattice {A : Finset α // A ∈ F} :=
  { inferInstanceAs (PartialOrder {A : Finset α // A ∈ F}) with
    sup := fun x y => ⟨x.1 ∪ y.1, hF _ x.2 _ y.2⟩
    inf := fun x y =>
      ⟨(F.filter (fun C => C ⊆ x.1 ∩ y.1)).sup id,
        sup_id_mem hF h0 (Finset.filter_subset _ _)⟩
    le_sup_left := fun x y => show x.1 ⊆ x.1 ∪ y.1 from Finset.subset_union_left
    le_sup_right := fun x y => show y.1 ⊆ x.1 ∪ y.1 from Finset.subset_union_right
    sup_le := fun x y z hx hy => show x.1 ∪ y.1 ⊆ z.1 from Finset.union_subset hx hy
    inf_le_left := fun x y => by
      show (F.filter (fun C => C ⊆ x.1 ∩ y.1)).sup id ≤ x.1
      apply Finset.sup_le
      intro C hC
      exact le_trans (Finset.mem_filter.mp hC).2 Finset.inter_subset_left
    inf_le_right := fun x y => by
      show (F.filter (fun C => C ⊆ x.1 ∩ y.1)).sup id ≤ y.1
      apply Finset.sup_le
      intro C hC
      exact le_trans (Finset.mem_filter.mp hC).2 Finset.inter_subset_right
    le_inf := fun x y z hxy hxz => by
      show x.1 ≤ (F.filter (fun C => C ⊆ y.1 ∩ z.1)).sup id
      exact Finset.le_sup (f := id)
        (Finset.mem_filter.mpr ⟨x.2, Finset.subset_inter hxy hxz⟩) }

/-- Core of the reverse direction, assuming `∅ ∈ F`.  Apply the meet-irreducible
lattice conjecture to the lattice `(F, ⊆)`: a meet-irreducible `m` has a least
strict upper bound `m⁺`; any `x ∈ m⁺ ∖ m` makes `m` the largest `x`-free member,
so the principal ideal `↓m` is exactly the `x`-free members.  The lattice bound
`2 |↓m| ≤ |F|` then says `x` is abundant. -/
theorem exists_isFranklElement_of_mem_empty (h : FranklLatticeMeet)
    {F : Finset (Finset α)} (hF : IsUnionClosed F) (h0 : ∅ ∈ F)
    (hne : HasNonemptyMember F) :
    ∃ x : α, IsFranklElement x F := by
  classical
  letI : Lattice {A : Finset α // A ∈ F} := ucLattice hF h0
  obtain ⟨N, hN, hNne⟩ := hne
  have hNne0 : (∅ : Finset α) ≠ N := fun he => hNne.ne_empty he.symm
  have hcard2 : 2 ≤ Nat.card {A : Finset α // A ∈ F} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have hsub : ({∅, N} : Finset (Finset α)) ⊆ F := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact h0
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hN
    calc (2 : ℕ) = ({∅, N} : Finset (Finset α)).card := (Finset.card_pair hNne0).symm
      _ ≤ F.card := Finset.card_le_card hsub
  obtain ⟨m, hm, hmcard⟩ := h {A : Finset α // A ∈ F} hcard2
  obtain ⟨m', hmm', hleast⟩ := InfIrred.exists_least_gt hm
  have hss : m.1 ⊂ m'.1 := hmm'
  obtain ⟨x, hxm', hxm⟩ := Finset.exists_of_ssubset hss
  -- `m.1` is exactly the set of `x`-free members
  have hclaim : ∀ A : Finset α, A ∈ F → (A ⊆ m.1 ↔ x ∉ A) := by
    intro A hA
    refine ⟨fun hAM hxA => hxm (hAM hxA), fun hxA => ?_⟩
    by_contra hnsub
    have hlt : m < (⟨m.1 ∪ A, hF _ m.2 _ hA⟩ : {A : Finset α // A ∈ F}) := by
      rw [lt_iff_le_and_ne]
      refine ⟨Finset.subset_union_left, fun he => ?_⟩
      have : m.1 = m.1 ∪ A := congrArg Subtype.val he
      exact hnsub (this ▸ Finset.subset_union_right)
    have hsub' : m'.1 ⊆ m.1 ∪ A := hleast _ hlt
    rcases Finset.mem_union.mp (hsub' hxm') with h1 | h1
    · exact hxm h1
    · exact hxA h1
  refine ⟨x, ?_, ?_⟩
  · rw [mem_familyUnion]; exact ⟨m'.1, m'.2, hxm'⟩
  · have hSF : Nat.card {A : Finset α // A ∈ F} = F.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have hkey : Nat.card {y : {A : Finset α // A ∈ F} // y ≤ m} =
        (F.filter (fun A => x ∉ A)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply Finset.card_bij (fun (y : {A : Finset α // A ∈ F}) _ => (y : Finset α))
      · intro y hy
        rw [Finset.mem_filter] at hy ⊢
        exact ⟨y.2, (hclaim y.1 y.2).mp hy.2⟩
      · intro y _ z _ hyz; exact Subtype.ext hyz
      · intro A hA
        rw [Finset.mem_filter] at hA
        exact ⟨⟨A, hA.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hclaim A hA.1).mpr hA.2⟩, rfl⟩
    rw [hkey, hSF] at hmcard
    have hsplit : memberCount x F + (F.filter (fun A => x ∉ A)).card = F.card := by
      rw [memberCount, memberSubfamily]
      exact Finset.card_filter_add_card_filter_not (s := F) (fun A => x ∈ A)
    omega

/-- **The meet-irreducible lattice conjecture implies the set conjecture.**
The `∅ ∉ F` case is reduced to `exists_isFranklElement_of_mem_empty` by passing
to `insert ∅ F`, which has the same element-counts. -/
theorem franklLatticeMeet_imp_franklConjecture (h : FranklLatticeMeet) :
    FranklConjecture := by
  intro α _ F hF hne
  classical
  have h0 : ∅ ∈ insert ∅ F := Finset.mem_insert_self _ _
  have hFsub : F ⊆ insert ∅ F := Finset.subset_insert _ _
  have hF'uc : IsUnionClosed (insert ∅ F) := by
    intro A hA B hB
    rcases Finset.mem_insert.mp hA with rfl | hA
    · rcases Finset.mem_insert.mp hB with rfl | hB
      · simp
      · simpa using Finset.mem_insert_of_mem hB
    · rcases Finset.mem_insert.mp hB with rfl | hB
      · simpa using Finset.mem_insert_of_mem hA
      · exact Finset.mem_insert_of_mem (hF A hA B hB)
  have hne' : HasNonemptyMember (insert ∅ F) := by
    obtain ⟨N, hN, hNne⟩ := hne; exact ⟨N, hFsub hN, hNne⟩
  obtain ⟨x, hxU, hxcard⟩ := exists_isFranklElement_of_mem_empty h hF'uc h0 hne'
  have hmc : memberCount x (insert ∅ F) = memberCount x F := by
    unfold memberCount memberSubfamily
    rw [Finset.filter_insert, if_neg (Finset.notMem_empty x)]
  refine ⟨x, ?_, ?_⟩
  · rw [mem_familyUnion] at hxU ⊢
    obtain ⟨A, hA, hxA⟩ := hxU
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact absurd hxA (Finset.notMem_empty x)
    · exact ⟨A, hA, hxA⟩
  · have hcardle : F.card ≤ (insert ∅ F).card := Finset.card_le_card hFsub
    rw [hmc] at hxcard
    omega

/-- The lattice conjecture implies the set conjecture. -/
theorem franklLattice_imp_franklConjecture (h : FranklLattice) : FranklConjecture :=
  franklLatticeMeet_imp_franklConjecture (franklLattice_iff_franklLatticeMeet.mp h)

/-- **Poonen's equivalence**: the union-closed (set) conjecture is equivalent to
its lattice form. -/
theorem franklConjecture_iff_franklLattice : FranklConjecture ↔ FranklLattice :=
  ⟨franklConjecture_imp_franklLattice, franklLattice_imp_franklConjecture⟩

/-- The set conjecture is equivalent to the meet-irreducible lattice form. -/
theorem franklConjecture_iff_franklLatticeMeet : FranklConjecture ↔ FranklLatticeMeet :=
  franklConjecture_iff_franklLattice.trans franklLattice_iff_franklLatticeMeet

end Frankl
