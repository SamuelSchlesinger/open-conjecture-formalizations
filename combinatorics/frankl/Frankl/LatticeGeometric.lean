import Frankl.LatticeRelComplement

/-!
# Frankl's lattice conjecture for geometric lattices

Reference: Reinhold, "Frankl's conjecture is true for lower semimodular lattices";
`research/frankl_negative_space_round.md` (geometric-lattice lead).

A **geometric lattice** is an atomistic, (upper-)semimodular lattice — the lattice
of flats of a simple matroid (e.g. partition lattices `Πₙ`, subspace lattices).
Geometric lattices are *relatively complemented*, so by
`franklLattice_witness_of_atom_relComplemented` every atom is a join-irreducible
Frankl witness, lying below at most half the lattice.

This file proves the relative-complement hypothesis directly from the two
**elementary** axioms that *define* an atomistic upper-semimodular lattice,
avoiding Mathlib's `IsAtomistic` / geometric-lattice classes (absent in
`v4.28.0`) and working only with `Lattice`, `OrderBot`, and `CovBy`:

* `hsm` (upper-semimodularity, covering form): `p ⊓ q ⋖ p → q ⋖ p ⊔ q`;
* `hat` (atomisticity, usable form): below any `x ≰ z` lies an atom `c ≤ x`,
  `c ≰ z`.

The heart is the **matroid exchange** property
(`atom_exchange_of_semimodular`): for atoms `a, c` with `a ≰ y` but `a ≤ y ⊔ c`,
one gets `c ≤ y ⊔ a`.  Semimodularity enters exactly once, turning the covering
`c ⊓ y ⋖ c` (holding because `c` is an atom with `c ⊓ y = ⊥`) into `y ⋖ c ⊔ y`;
the covering then pins `y ⊔ a = y ⊔ c`.  Relative complementation
(`exists_relComplement_of_geometric`) follows by taking `y` maximal among
elements `≤ x` not above `a`: maximality plus exchange and the atomistic axiom
force `a ⊔ y = x`.

This case is *incomparable* to the modular case (`franklLattice_of_modular`): it
covers the genuinely non-modular geometric lattices (partition lattices) that the
modular case misses, at the cost of assuming atomisticity.
-/

set_option autoImplicit false

namespace Frankl

variable {L : Type*} [Lattice L] [OrderBot L]

/-- **Atom meet helper.**  If `c` is an atom and `c ≰ y`, then `c ⊓ y = ⊥`:
`c ⊓ y ≤ c` and `c ⊓ y ≠ c` (else `c ≤ y`), so `c ⊓ y < c`, and an atom has
nothing strictly below it but `⊥`. -/
theorem atom_inf_eq_bot {c y : L} (hc : IsAtom c) (hcy : ¬ c ≤ y) :
    c ⊓ y = ⊥ := by
  have hlt : c ⊓ y < c :=
    lt_of_le_of_ne inf_le_left (fun h => hcy (h ▸ inf_le_right))
  exact hc.2 _ hlt

/-- **Matroid exchange for atoms.**  In an upper-semimodular lattice, for atoms
`a`, `c` with `a ≰ y` but `a ≤ y ⊔ c`, one has `c ≤ y ⊔ a`.

`c ≰ y` (else `y ⊔ c = y ≥ a`); hence `c ⊓ y = ⊥` and `c ⊓ y ⋖ c`, so
semimodularity gives `y ⋖ c ⊔ y = y ⊔ c`.  Then `y < y ⊔ a ≤ y ⊔ c` and the
covering force `y ⊔ a = y ⊔ c`, whence `c ≤ y ⊔ c = y ⊔ a`. -/
theorem atom_exchange_of_semimodular (hsm : ∀ p q : L, p ⊓ q ⋖ p → q ⋖ p ⊔ q)
    {a c y : L} (_ha : IsAtom a) (hc : IsAtom c)
    (hay : ¬ a ≤ y) (hayc : a ≤ y ⊔ c) :
    c ≤ y ⊔ a := by
  have hcy : ¬ c ≤ y := by
    intro hcyle
    exact hay ((by rw [sup_eq_left.mpr hcyle] : (y ⊔ c : L) = y) ▸ hayc)
  have hbot : c ⊓ y = ⊥ := atom_inf_eq_bot hc hcy
  have hcov_c : c ⊓ y ⋖ c := by rw [hbot]; exact hc.bot_covBy
  have hcov : y ⋖ c ⊔ y := hsm c y hcov_c
  rw [sup_comm] at hcov
  have hlt : y < y ⊔ a := left_lt_sup.mpr hay
  have hle : y ⊔ a ≤ y ⊔ c := sup_le le_sup_left hayc
  have heq : y ⊔ a = y ⊔ c := by
    rcases hle.eq_or_lt with h | h
    · exact h
    · exact absurd h (hcov.2 hlt)
  rw [heq]; exact le_sup_right

/-- **Relative complementation from the geometric axioms.**  In a finite
atomistic upper-semimodular lattice, every `x ≥ a` (with `a` an atom) admits a
relative complement of `a`: some `y` with `a ⊓ y = ⊥` and `a ⊔ y = x`.

Take `y` maximal among elements `≤ x` with `a ≰ y` (`⊥` qualifies).  Then
`a ⊓ y = ⊥`; and if `a ⊔ y ≠ x` then `x ≰ a ⊔ y`, so atomisticity gives an atom
`c ≤ x`, `c ≰ a ⊔ y`; exchange forces `a ≰ y ⊔ c`, so `y ⊔ c` lies in the set and
strictly exceeds `y` — contradicting maximality.  Hence `a ⊔ y = x`. -/
theorem exists_relComplement_of_geometric
    (hsm : ∀ p q : L, p ⊓ q ⋖ p → q ⋖ p ⊔ q)
    (hat : ∀ x z : L, ¬ x ≤ z → ∃ c, IsAtom c ∧ c ≤ x ∧ ¬ c ≤ z)
    [Finite L] {a : L} (ha : IsAtom a) :
    ∀ x : L, a ≤ x → ∃ y : L, a ⊓ y = ⊥ ∧ a ⊔ y = x := by
  classical
  have : Fintype L := Fintype.ofFinite L
  intro x hax
  set S : Finset L := Finset.univ.filter (fun y => y ≤ x ∧ ¬ a ≤ y) with hS
  have hbotmem : (⊥ : L) ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, bot_le, fun h => ha.1 (le_bot_iff.mp h)⟩
  obtain ⟨y₀, hy₀max⟩ := S.exists_maximal ⟨⊥, hbotmem⟩
  have hy₀x : y₀ ≤ x := (Finset.mem_filter.mp hy₀max.1).2.1
  have hay₀ : ¬ a ≤ y₀ := (Finset.mem_filter.mp hy₀max.1).2.2
  refine ⟨y₀, atom_inf_eq_bot ha hay₀, ?_⟩
  have hle : a ⊔ y₀ ≤ x := sup_le hax hy₀x
  by_contra hne
  have hxnle : ¬ x ≤ a ⊔ y₀ := not_le_of_gt (lt_of_le_of_ne hle hne)
  obtain ⟨c, hc, hcx, hcay₀⟩ := hat x (a ⊔ y₀) hxnle
  have hcy₀ : ¬ c ≤ y₀ := fun h => hcay₀ (h.trans le_sup_right)
  have hay₀c : ¬ a ≤ y₀ ⊔ c := by
    intro hle'
    exact hcay₀ (by rw [sup_comm]; exact atom_exchange_of_semimodular hsm ha hc hay₀ hle')
  have hmem' : y₀ ⊔ c ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, sup_le hy₀x hcx, hay₀c⟩
  exact (not_le_of_gt (left_lt_sup.mpr hcy₀)) (hy₀max.2 hmem' le_sup_left)

/-- **Frankl's conjecture for geometric lattices (atom witness).**  In a finite
atomistic upper-semimodular lattice, every atom `a` is a join-irreducible Frankl
witness: `2 · |↑a| ≤ |L|`.

The genuinely new, non-modular semimodular case (e.g. partition lattices),
obtained by deriving relative complementation from the elementary geometric
axioms and applying `franklLattice_witness_of_atom_relComplemented`. -/
theorem franklLattice_witness_of_atom_geometric
    {L : Type*} [Lattice L] [OrderBot L] [Finite L]
    (hsm : ∀ p q : L, p ⊓ q ⋖ p → q ⋖ p ⊔ q)
    (hat : ∀ x z : L, ¬ x ≤ z → ∃ c, IsAtom c ∧ c ≤ x ∧ ¬ c ≤ z)
    {a : L} (ha : IsAtom a) :
    SupIrred a ∧ 2 * Nat.card {x : L // a ≤ x} ≤ Nat.card L :=
  franklLattice_witness_of_atom_relComplemented ha
    (exists_relComplement_of_geometric hsm hat ha)

end Frankl
