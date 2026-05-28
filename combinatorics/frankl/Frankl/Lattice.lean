import Mathlib.Order.Irreducible
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

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

end Frankl
