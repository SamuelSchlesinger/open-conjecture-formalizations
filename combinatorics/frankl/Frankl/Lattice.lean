import Mathlib.Order.Irreducible
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic
import Frankl.Basic

/-!
# The lattice form of Frankl's union-closed sets conjecture

Reference: B. Poonen, "Union-closed families", J. Combin. Theory Ser. A 59
(1992); H. Bruhn, O. Schaudt, "The journey of the union-closed sets
conjecture", Graphs and Combinatorics 31 (2015); see also
arXiv:2503.00277 for the lattice formulation.

Poonen's reformulation states that Frankl's conjecture is equivalent to the
following lattice statement:

> Every finite lattice `L` with at least two elements contains a
> join-irreducible element `j` lying below at most half of the elements,
> i.e. `2 * |{x : j ≤ x}| ≤ |L|`.

Here "join-irreducible" is Mathlib's `SupIrred` (`¬ IsMin j` and
`b ⊔ c = j → b = j ∨ c = j`), and `{x : j ≤ x}` is the principal up-set `↑j`.

This file:

* states the lattice conjecture `FranklLattice`;
* proves the **distributive case** completely (`franklLattice_of_distribLattice`),
  a known class for Frankl's conjecture, by an elementary Birkhoff-free argument.

The equivalence with the set form (`Frankl.FranklConjecture`) and the
semimodular/modular cases are left as future work.
-/

set_option autoImplicit false

namespace Frankl

open Finset

/-- **Lattice form of Frankl's conjecture** (Poonen).  Every finite lattice with
at least two elements has a join-irreducible element below at most half of the
elements. -/
def FranklLattice : Prop :=
  ∀ (L : Type) [Lattice L] [Finite L],
    2 ≤ Nat.card L →
      ∃ j : L, SupIrred j ∧ 2 * Nat.card {x : L // j ≤ x} ≤ Nat.card L

/-- The **distributive case** of the lattice form of Frankl's conjecture, a known
class for the union-closed conjecture.

Elementary, Birkhoff-free proof.  Choose a *maximal* join-irreducible `j`.  For
`x` define `f x := ⨆ {y ≤ x : ¬ j ≤ y}`.  Distributivity makes `j` join-prime,
so `¬ j ≤ f x`; and maximality of `j` makes every join-irreducible `k ≤ x`
either equal to `j` or `≤ f x`, whence `x = f x ⊔ j`.  Thus `x ↦ f x` injects
the up-set `{x : j ≤ x}` into its complement, so the up-set has at most half the
elements. -/
theorem franklLattice_of_distribLattice
    {L : Type*} [DistribLattice L] [Finite L] (hL : 2 ≤ Nat.card L) :
    ∃ j : L, SupIrred j ∧ 2 * Nat.card {x : L // j ≤ x} ≤ Nat.card L := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card L = Nat.card L := Nat.card_eq_fintype_card.symm
  have hL' : 2 ≤ Fintype.card L := by rw [hcard]; exact hL
  haveI : Nontrivial L := Fintype.one_lt_card_iff_nontrivial.mp hL'
  haveI : OrderBot L := Fintype.toOrderBot L
  -- join-irreducibles exist: decompose an element ≠ ⊥
  obtain ⟨a₀, ha₀⟩ := exists_ne (⊥ : L)
  obtain ⟨s₀, hs₀, hsi₀⟩ := exists_supIrred_decomposition a₀
  have hSIne : (univ.filter (fun a : L => SupIrred a)).Nonempty := by
    by_cases h : s₀.Nonempty
    · obtain ⟨b, hb⟩ := h
      exact ⟨b, mem_filter.mpr ⟨mem_univ _, hsi₀ hb⟩⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sup_empty] at hs₀
      exact absurd hs₀.symm ha₀
  -- choose a maximal join-irreducible j
  obtain ⟨j, hjmax⟩ := Finset.exists_maximal hSIne
  have hj : SupIrred j := (mem_filter.mp hjmax.1).2
  have hjp : SupPrime j := supPrime_iff_supIrred.mpr hj
  -- j absorbs every join-irreducible above it
  have hmax : ∀ k : L, SupIrred k → j ≤ k → k = j := by
    intro k hk hjk
    exact le_antisymm (hjmax.2 (mem_filter.mpr ⟨mem_univ _, hk⟩) hjk) hjk
  -- the "lower part" map f and its properties
  set f : L → L := fun x => (univ.filter (fun y => y ≤ x ∧ ¬ j ≤ y)).sup id with hf
  have hf_le : ∀ x, f x ≤ x := fun x =>
    Finset.sup_le fun y hy => (mem_filter.mp hy).2.1
  have hf_not : ∀ x, ¬ j ≤ f x := by
    intro x hjfx
    obtain ⟨y, hy, hjy⟩ := (SupPrime.le_finset_sup hjp).mp hjfx
    exact (mem_filter.mp hy).2.2 hjy
  -- every x is recovered as `f x ⊔ j`
  have hle : ∀ x, x ≤ f x ⊔ j := by
    intro x
    obtain ⟨s, hs, hsi⟩ := exists_supIrred_decomposition x
    calc x = s.sup id := hs.symm
      _ ≤ f x ⊔ j := by
          refine Finset.sup_le fun k hk => ?_
          have hkx : k ≤ x := by rw [← hs]; exact Finset.le_sup (f := id) hk
          by_cases hjk : j ≤ k
          · have hkj : k = j := hmax k (hsi hk) hjk
            rw [hkj]; exact le_sup_right
          · have hk_fx : k ≤ f x :=
              Finset.le_sup (f := id) (mem_filter.mpr ⟨mem_univ _, hkx, hjk⟩)
            exact le_sup_of_le_left hk_fx
  have hxeq : ∀ x, j ≤ x → x = f x ⊔ j := fun x hx =>
    le_antisymm (hle x) (sup_le (hf_le x) hx)
  -- inject the up-set of j into its complement
  refine ⟨j, hj, ?_⟩
  have hmaps : Set.MapsTo f (univ.filter (fun x => j ≤ x)) (univ.filter (fun x => ¬ j ≤ x)) := by
    intro x _
    exact mem_filter.mpr ⟨mem_univ _, hf_not x⟩
  have hinj : Set.InjOn f (univ.filter (fun x => j ≤ x)) := by
    intro x hx y hy hxy
    have hjx : j ≤ x := (mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hjy : j ≤ y := (mem_filter.mp (Finset.mem_coe.mp hy)).2
    calc x = f x ⊔ j := hxeq x hjx
      _ = f y ⊔ j := by rw [hxy]
      _ = y := (hxeq y hjy).symm
  have hcard_le :
      (univ.filter (fun x => j ≤ x)).card ≤ (univ.filter (fun x => ¬ j ≤ x)).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hsplit :
      (univ.filter (fun x => j ≤ x)).card + (univ.filter (fun x => ¬ j ≤ x)).card =
        Fintype.card L := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hconv : Nat.card {x : L // j ≤ x} = (univ.filter (fun x => j ≤ x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hconv, ← hcard]
  omega

/-- The lattice form of Frankl's conjecture holds for finite linear orders
(chains), as a special case of the distributive lattice result. -/
theorem franklLattice_of_linearOrder
    {L : Type*} [LinearOrder L] [Finite L] (hL : 2 ≤ Nat.card L) :
    ∃ j : L, SupIrred j ∧ 2 * Nat.card {x : L // j ≤ x} ≤ Nat.card L :=
  franklLattice_of_distribLattice hL

/-- The **modular case** of the lattice form of Frankl's conjecture (Abe–Nakano),
which strictly generalises the distributive case.

Take `m` maximal among the proper elements (so `m < z` forces `z = ⊤`) and a
join-irreducible `x ⊄ m` (one exists because `⊤` is the join of the
join-irreducibles).  Then `x ⊔ m = ⊤`, and the map `α ↦ m ⊓ α` injects the
up-set `↑x` into its complement: it is injective because modularity gives
`x ⊔ (m ⊓ α) = (x ⊔ m) ⊓ α = α` for `α ≥ x`, and its image avoids `↑x` since
`m ⊓ α ≤ m ⊉ x`.  Hence `2 |↑x| ≤ |L|`. -/
theorem franklLattice_of_modular
    {L : Type*} [Lattice L] [IsModularLattice L] [Finite L] (hL : 2 ≤ Nat.card L) :
    ∃ x : L, SupIrred x ∧ 2 * Nat.card {z : L // x ≤ z} ≤ Nat.card L := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card L = Nat.card L := Nat.card_eq_fintype_card.symm
  have hL' : 2 ≤ Fintype.card L := by rw [hcard]; exact hL
  haveI : Nontrivial L := Fintype.one_lt_card_iff_nontrivial.mp hL'
  haveI : BoundedOrder L := Fintype.toBoundedOrder L
  -- a maximal proper element `m`
  have hpropne : (univ.filter (fun z : L => z ≠ ⊤)).Nonempty :=
    ⟨⊥, mem_filter.mpr ⟨mem_univ _, bot_ne_top⟩⟩
  obtain ⟨m, hmmax⟩ := Finset.exists_maximal hpropne
  have hmne : m ≠ ⊤ := (mem_filter.mp hmmax.1).2
  have hmtop : ∀ z : L, m < z → z = ⊤ := by
    intro z hz
    by_contra hzne
    exact absurd (le_antisymm hz.le (hmmax.2 (mem_filter.mpr ⟨mem_univ _, hzne⟩) hz.le))
      (ne_of_lt hz)
  -- a join-irreducible `x` not below `m`
  obtain ⟨s, hs, hsi⟩ := exists_supIrred_decomposition (⊤ : L)
  have hxex : ∃ x ∈ s, ¬ x ≤ m := by
    by_contra hall
    push_neg at hall
    have htop : (⊤ : L) ≤ m := by
      rw [← hs]; exact Finset.sup_le fun x hx => by simpa using hall x hx
    exact hmne (top_le_iff.mp htop)
  obtain ⟨x, hxs, hxm⟩ := hxex
  have hmx : x ⊔ m = ⊤ :=
    hmtop _ (lt_of_le_of_ne le_sup_right fun he => hxm (le_sup_left.trans he.ge))
  refine ⟨x, hsi hxs, ?_⟩
  -- the injection `α ↦ m ⊓ α` of `↑x` into its complement
  have hrec : ∀ α : L, x ≤ α → x ⊔ m ⊓ α = α := by
    intro α hα; rw [← sup_inf_assoc_of_le m hα, hmx, top_inf_eq]
  have hmaps : Set.MapsTo (fun α => m ⊓ α)
      (univ.filter (fun z => x ≤ z)) (univ.filter (fun z => ¬ x ≤ z)) := by
    intro α _
    exact mem_filter.mpr ⟨mem_univ _, fun hxle => hxm (le_trans hxle inf_le_left)⟩
  have hinj : Set.InjOn (fun α => m ⊓ α) (univ.filter (fun z => x ≤ z)) := by
    intro α hα β hβ hαβ
    have hxα : x ≤ α := (mem_filter.mp (Finset.mem_coe.mp hα)).2
    have hxβ : x ≤ β := (mem_filter.mp (Finset.mem_coe.mp hβ)).2
    have hαβ' : m ⊓ α = m ⊓ β := hαβ
    calc α = x ⊔ m ⊓ α := (hrec α hxα).symm
      _ = x ⊔ m ⊓ β := by rw [hαβ']
      _ = β := hrec β hxβ
  have hcard_le :
      (univ.filter (fun z => x ≤ z)).card ≤ (univ.filter (fun z => ¬ x ≤ z)).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hsplit :
      (univ.filter (fun z => x ≤ z)).card + (univ.filter (fun z => ¬ x ≤ z)).card =
        Fintype.card L := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hconv : Nat.card {z : L // x ≤ z} = (univ.filter (fun z => x ≤ z)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hconv, ← hcard]
  omega

open Classical in
/-- In a finite lattice every element is the join of the join-irreducible
elements below it. -/
theorem sup_filter_supIrred_le {L : Type*} [Lattice L] [Fintype L] [OrderBot L]
    (a : L) :
    (Finset.univ.filter (fun j : L => SupIrred j ∧ j ≤ a)).sup id = a := by
  refine le_antisymm (Finset.sup_le fun j hj => (mem_filter.mp hj).2.2) ?_
  obtain ⟨s, hs, hsi⟩ := exists_supIrred_decomposition a
  calc a = s.sup id := hs.symm
    _ ≤ (Finset.univ.filter (fun j : L => SupIrred j ∧ j ≤ a)).sup id := by
        refine Finset.sup_le fun k hk => ?_
        have hka : k ≤ a := (Finset.le_sup (f := id) hk).trans hs.le
        exact Finset.le_sup (f := id) (mem_filter.mpr ⟨mem_univ _, hsi hk, hka⟩)

/-- **The set conjecture implies the lattice conjecture.**

Given a finite lattice `L` with `|L| ≥ 2`, build the union-closed family on the
ground set `J(L)` of join-irreducibles whose members are
`f a = {j ∈ J(L) : ¬ j ≤ a}` for `a ∈ L`.  Since `f a ∪ f b = f (a ⊓ b)` this is
union-closed, `f` is injective (an element is the join of the join-irreducibles
below it), so `|family| = |L|`, and a join-irreducible `j₀` lies in `f a` for
exactly `|L| − |↑j₀|` values of `a`.  A Frankl element of this family is thus a
join-irreducible `j₀` with `2 |↑j₀| ≤ |L|`. -/
theorem franklConjecture_imp_franklLattice (h : FranklConjecture) : FranklLattice := by
  intro L _ _ hL
  classical
  haveI : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card L = Nat.card L := Nat.card_eq_fintype_card.symm
  have hL' : 2 ≤ Fintype.card L := by rw [hcard]; exact hL
  haveI : Nontrivial L := Fintype.one_lt_card_iff_nontrivial.mp hL'
  haveI : OrderBot L := Fintype.toOrderBot L
  -- the family `f a = {j join-irreducible : ¬ j ≤ a}` on ground set `J(L)`
  set J := {j : L // SupIrred j} with hJ
  let f : L → Finset J := fun a => univ.filter (fun j => ¬ (j : L) ≤ a)
  have hfmem : ∀ (a : L) (j : J), j ∈ f a ↔ ¬ (j : L) ≤ a := by
    intro a j; simp only [f, mem_filter, mem_univ, true_and]
  -- `f` turns meet into union
  have hf_union : ∀ a b : L, f a ∪ f b = f (a ⊓ b) := by
    intro a b
    ext j
    simp only [Finset.mem_union, hfmem, le_inf_iff, not_and_or]
  -- `f` is injective
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hiff : ∀ j : L, SupIrred j → (j ≤ a ↔ j ≤ b) := by
      intro j hj
      have hmem : (⟨j, hj⟩ : J) ∈ f a ↔ (⟨j, hj⟩ : J) ∈ f b := by rw [hab]
      rw [hfmem, hfmem] at hmem
      exact not_iff_not.mp hmem
    have : (univ.filter (fun j : L => SupIrred j ∧ j ≤ a)) =
        (univ.filter (fun j : L => SupIrred j ∧ j ≤ b)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and]
      exact and_congr_right fun hj => hiff j hj
    have ha := sup_filter_supIrred_le a
    have hb := sup_filter_supIrred_le b
    rw [← ha, ← hb, this]
  -- a join-irreducible exists, so the `⊥`-member is nonempty
  obtain ⟨a₀, ha₀⟩ := exists_ne (⊥ : L)
  obtain ⟨s, hs, hsi⟩ := exists_supIrred_decomposition a₀
  have hbot_irred : ∃ j₀ : J, True := by
    by_cases hse : s.Nonempty
    · obtain ⟨b, hb⟩ := hse
      exact ⟨⟨b, hsi hb⟩, trivial⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hse
      rw [hse, Finset.sup_empty] at hs
      exact absurd hs.symm ha₀
  obtain ⟨j₀, -⟩ := hbot_irred
  -- the union-closed family
  set 𝓕 : Finset (Finset J) := univ.image f with h𝓕
  have huc : IsUnionClosed 𝓕 := by
    intro A hA B hB
    simp only [h𝓕, mem_image, mem_univ, true_and] at hA hB ⊢
    obtain ⟨a, rfl⟩ := hA
    obtain ⟨b, rfl⟩ := hB
    exact ⟨a ⊓ b, (hf_union a b).symm⟩
  have hne : HasNonemptyMember 𝓕 := by
    refine ⟨f ⊥, ?_, ?_⟩
    · simp only [h𝓕, mem_image, mem_univ, true_and]; exact ⟨⊥, rfl⟩
    · refine ⟨j₀, ?_⟩
      rw [hfmem]
      exact fun hle => j₀.2.ne_bot (le_bot_iff.mp hle)
  -- apply the set conjecture
  obtain ⟨x, -, hxcard⟩ := h 𝓕 huc hne
  refine ⟨x, x.2, ?_⟩
  -- compute `memberCount x 𝓕 = |{a : ¬ x ≤ a}|`
  have hmember : memberCount x 𝓕 = (univ.filter (fun a : L => ¬ (x : L) ≤ a)).card := by
    have hset : memberSubfamily x 𝓕 = (univ.filter (fun a : L => x ∈ f a)).image f := by
      ext A
      simp only [memberSubfamily, h𝓕, mem_filter, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨⟨a, rfl⟩, hx⟩; exact ⟨a, hx, rfl⟩
      · rintro ⟨a, hx, rfl⟩; exact ⟨⟨a, rfl⟩, hx⟩
    rw [memberCount, hset, Finset.card_image_of_injective _ hf_inj]
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, hfmem]
  -- `|𝓕| = |L|`
  have hcardF : 𝓕.card = Fintype.card L := by
    rw [h𝓕, Finset.card_image_of_injective _ hf_inj, Finset.card_univ]
  -- split and conclude
  have hsplit : (univ.filter (fun a : L => ¬ (x : L) ≤ a)).card +
      (univ.filter (fun a : L => (x : L) ≤ a)).card = Fintype.card L := by
    rw [add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hconv : Nat.card {y : L // (x : L) ≤ y} =
      (univ.filter (fun a : L => (x : L) ≤ a)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hconv, ← hcard]
  rw [hmember, hcardF] at hxcard
  omega

/-- **Meet-irreducible (dual) form of the lattice conjecture.**  Every finite
lattice with at least two elements has a meet-irreducible element above at most
half of the elements.  This is the formulation Poonen proved equivalent to the
union-closed conjecture; it is the order dual of `FranklLattice`. -/
def FranklLatticeMeet : Prop :=
  ∀ (L : Type) [Lattice L] [Finite L],
    2 ≤ Nat.card L →
      ∃ m : L, InfIrred m ∧ 2 * Nat.card {x : L // x ≤ m} ≤ Nat.card L

/-- The join-irreducible and meet-irreducible forms of the lattice conjecture are
equivalent, by order duality. -/
theorem franklLattice_iff_franklLatticeMeet : FranklLattice ↔ FranklLatticeMeet := by
  constructor
  · intro h L _ _ hL
    obtain ⟨j, hj, hcard⟩ := h Lᵒᵈ hL
    exact ⟨OrderDual.ofDual j, infIrred_ofDual.mpr hj, hcard⟩
  · intro h L _ _ hL
    obtain ⟨m, hm, hcard⟩ := h Lᵒᵈ hL
    exact ⟨OrderDual.ofDual m, supIrred_ofDual.mpr hm, hcard⟩

end Frankl
