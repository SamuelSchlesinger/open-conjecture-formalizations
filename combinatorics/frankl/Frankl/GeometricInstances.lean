import Frankl.LatticeGeometric
import Mathlib.Data.Finset.Grade

/-!
# The powerset (Boolean) lattice is geometric — concrete witness

This file is the **non-vacuousness witness** for the geometric branch of Frankl's
conjecture proved in `Frankl/LatticeGeometric.lean`.  The abstract theorem
`franklLattice_witness_of_atom_geometric` assumes two *elementary* axioms of a
finite atomistic upper-semimodular (geometric) lattice:

* `hsm` (upper-semimodularity, covering form): `p ⊓ q ⋖ p → q ⋖ p ⊔ q`;
* `hat` (atomisticity, usable form): below any `x ≰ z` lies an atom `c ≤ x`,
  `c ≰ z`.

Here we exhibit a concrete model: the **powerset lattice** `Finset α`.  On it the
lattice meet is intersection, the join is union, `⊥ = ∅`, and `≤` is `⊆`.  This
lattice is distributive (hence modular, hence upper-semimodular) and atomistic
(every set is the union of its singletons, which are precisely the atoms), so it
*is* geometric.  Concretely:

* `atomistic_finset` proves the atomistic axiom `hat`: a set not contained in `z`
  contains some element `a`, and the singleton `{a}` is an atom below it but not
  below `z`.
* `upperSemimodular_finset` proves the covering axiom `hsm` by the explicit
  description of covers in a powerset (`s ⋖ t` iff `t = insert a s` for some
  `a ∉ s`).
* `franklLattice_witness_singleton_finset` instantiates the abstract theorem at
  the atom `{a}`, yielding `SupIrred {a}` and the Frankl bound
  `2 · |↑{a}| ≤ |Finset α|`.

The optional `isUpperSemimodular_of_modular` lemma shows more generally that
*every* modular lattice satisfies the covering axiom, via the diamond
order-isomorphism `infIccOrderIsoIccSup` (which preserves `CovBy`).  The powerset
result `upperSemimodular_finset` is obtained directly from the powerset cover
characterisation, independently of this general fact.

Reference: `Frankl/LatticeGeometric.lean` (abstract geometric theorem);
Mathlib `Mathlib.Data.Finset.Grade` (powerset covers and atoms),
`Mathlib.Order.ModularLattice` (diamond isomorphism).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Frankl

/-! ## The atomistic axiom for the powerset lattice -/

/-- **Atomistic axiom `hat` for `Finset α`.**  If `x ⊄ z` then there is an atom
`c = {a}` with `c ≤ x` and `c ≰ z`.  Indeed `x ⊄ z` yields (`Finset.not_subset`)
an `a ∈ x` with `a ∉ z`; the singleton `{a}` is an atom (`Finset.isAtom_singleton`),
`{a} ⊆ x` because `a ∈ x` (`Finset.singleton_subset_iff`), and `{a} ⊄ z` because
otherwise `a ∈ z`. -/
theorem atomistic_finset {α : Type*} [DecidableEq α] :
    ∀ x z : Finset α, ¬ x ≤ z → ∃ c, IsAtom c ∧ c ≤ x ∧ ¬ c ≤ z := by
  intro x z hxz
  obtain ⟨a, hax, haz⟩ := Finset.not_subset.mp hxz
  refine ⟨{a}, Finset.isAtom_singleton a, ?_, ?_⟩
  · exact Finset.singleton_subset_iff.mpr hax
  · intro hsub
    exact haz (Finset.singleton_subset_iff.mp hsub)

/-! ## The upper-semimodularity axiom for the powerset lattice -/

/-- **Upper-semimodularity axiom `hsm` for `Finset α`.**  If `s ⊓ t ⋖ s` then
`t ⋖ s ⊔ t`, where `⊓ = ∩` and `⊔ = ∪`.

A cover in a powerset adds exactly one element: from `s ∩ t ⋖ s` we get
(`CovBy.exists_finset_insert`) an `a ∉ s ∩ t` with `insert a (s ∩ t) = s`.  Then
`a ∈ s` and `a ∉ t` (else `a ∈ s ∩ t`).  Consequently `s ∪ t = insert a t` and
`a ∉ t`, so `t ⋖ insert a t = s ∪ t` by `Finset.covBy_insert`. -/
theorem upperSemimodular_finset {α : Type*} [DecidableEq α] :
    ∀ s t : Finset α, s ⊓ t ⋖ s → t ⋖ s ⊔ t := by
  intro s t hcov
  obtain ⟨a, ha, hins⟩ := CovBy.exists_finset_insert hcov
  -- `s ⊓ t = s ∩ t`, `s ⊔ t = s ∪ t` definitionally on `Finset`.
  have hinstInter : insert a (s ∩ t) = s := hins
  have haNotInter : a ∉ s ∩ t := ha
  have has : a ∈ s := hinstInter ▸ Finset.mem_insert_self a (s ∩ t)
  have hat : a ∉ t := by
    intro hatt
    exact haNotInter (Finset.mem_inter.mpr ⟨has, hatt⟩)
  -- `s ∪ t = insert a t`.
  have hunion : s ∪ t = insert a t := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with hxs | hxt
      · -- `x ∈ s = insert a (s ∩ t)`, so `x = a` or `x ∈ s ∩ t ⊆ t`.
        rw [← hinstInter] at hxs
        rcases Finset.mem_insert.mp hxs with hxa | hxinter
        · exact hxa ▸ Finset.mem_insert_self a t
        · exact Finset.mem_insert_of_mem (Finset.mem_inter.mp hxinter).2
      · exact Finset.mem_insert_of_mem hxt
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxt
      · exact hxa ▸ Finset.mem_union_left t has
      · exact Finset.mem_union_right s hxt
  have hcovUnion : t ⋖ s ⊔ t := by
    show t ⋖ s ∪ t
    rw [hunion]
    exact Finset.covBy_insert hat
  exact hcovUnion

/-! ## The Frankl witness for a singleton atom of the powerset lattice -/

/-- **Frankl witness for the powerset lattice.**  The singleton `{a}` is a
sup-irreducible Frankl witness in `Finset α`: it is join-irreducible and lies
below at most half of the lattice, `2 · |↑{a}| ≤ |Finset α|`.

This is the concrete instantiation of the abstract geometric theorem
`franklLattice_witness_of_atom_geometric` at the model `L := Finset α`, the atom
`{a}` (`Finset.isAtom_singleton`), and the two axioms proved above.  `[Fintype α]`
makes `Finset α` finite, supplying the required `[Finite (Finset α)]`. -/
theorem franklLattice_witness_singleton_finset
    {α : Type*} [DecidableEq α] [Fintype α] (a : α) :
    SupIrred ({a} : Finset α) ∧
      2 * Nat.card {x : Finset α // {a} ≤ x} ≤ Nat.card (Finset α) :=
  franklLattice_witness_of_atom_geometric
    upperSemimodular_finset atomistic_finset (Finset.isAtom_singleton a)

/-! ## Optional bonus: every modular lattice is upper-semimodular -/

/-- **Modular ⟹ upper-semimodular.**  In any modular lattice the covering axiom
`hsm` holds: `p ⊓ q ⋖ p → q ⋖ p ⊔ q`.

The diamond order-isomorphism `infIccOrderIsoIccSup p q : Icc (p ⊓ q) p ≃o
Icc q (p ⊔ q)` sends the endpoint `p ⊓ q` to `q` and `p` to `p ⊔ q`.  Order
isomorphisms preserve `CovBy` (`apply_covBy_apply_iff`), and covers inside an
interval `Icc` correspond to covers in `L` (the subtype coercion is an order
embedding with order-connected range).  Thus `p ⊓ q ⋖ p` transports to
`q ⋖ p ⊔ q`. -/
theorem isUpperSemimodular_of_modular {L : Type*} [Lattice L] [IsModularLattice L] :
    ∀ p q : L, p ⊓ q ⋖ p → q ⋖ p ⊔ q := by
  intro p q hcov
  -- Covers inside the interval `Icc lo hi` correspond to covers in `L`, since the
  -- coercion is an order embedding with order-connected range (`Set.ordConnected_Icc`).
  have icc_covBy {lo hi : L} (u v : Set.Icc lo hi) : (↑u : L) ⋖ ↑v ↔ u ⋖ v := by
    refine Set.OrdConnected.apply_covBy_apply_iff
      (OrderEmbedding.subtype fun c => c ∈ Set.Icc lo hi) ?_
    simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype, Set.setOf_mem_eq]
      using Set.ordConnected_Icc
  -- The diamond order-iso `Icc (p ⊓ q) p ≃o Icc q (p ⊔ q)`.
  set e := infIccOrderIsoIccSup p q with he
  -- `p ⊓ q` and `p` as members of `Icc (p ⊓ q) p`.
  let x₀ : Set.Icc (p ⊓ q) p := ⟨p ⊓ q, le_refl _, inf_le_left⟩
  let x₁ : Set.Icc (p ⊓ q) p := ⟨p, inf_le_left, le_refl _⟩
  -- The cover `p ⊓ q ⋖ p` inside the interval `Icc (p ⊓ q) p`.
  have hcovSub : x₀ ⋖ x₁ := (icc_covBy x₀ x₁).mp hcov
  -- Transport along the diamond iso: `e x₀ ⋖ e x₁` in `Icc q (p ⊔ q)`.
  have hcovImg : e x₀ ⋖ e x₁ := (apply_covBy_apply_iff e).mpr hcovSub
  -- Compute the images: `e x₀ = q`, `e x₁ = p ⊔ q` (as elements of the interval).
  have hx₀ : (e x₀ : L) = q := by
    simp only [he, infIccOrderIsoIccSup_apply_coe, x₀]
    rw [sup_eq_right.mpr inf_le_right]
  have hx₁ : (e x₁ : L) = p ⊔ q := by
    simp only [he, infIccOrderIsoIccSup_apply_coe, x₁]
  -- Pull the cover back down to `L` via the interval coercion.
  have hL : (↑(e x₀) : L) ⋖ ↑(e x₁) := (icc_covBy (e x₀) (e x₁)).mpr hcovImg
  rwa [hx₀, hx₁] at hL

end Frankl
