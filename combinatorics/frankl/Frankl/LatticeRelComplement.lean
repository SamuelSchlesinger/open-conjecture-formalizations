import Frankl.Lattice
import Mathlib.Order.Atoms
import Mathlib.Order.ModularLattice

/-!
# Frankl's lattice conjecture for relatively-complemented atoms

Reference: `research/frankl_negative_space_round.md` (geometric-lattice lead);
Reinhold, "Frankl's conjecture is true for lower semimodular lattices".

This file isolates the **mechanism** behind the geometric-lattice case of Frankl
(verified empirically in the workflow: in any atomistic upper-semimodular lattice
every atom lies below at most half the elements).  The mechanism is *relative
complementation*, and it needs **no semimodularity**:

> If `a` is an atom and every `x ≥ a` admits a relative complement `y` of `a` in
> `[⊥, x]` (i.e. `a ⊓ y = ⊥` and `a ⊔ y = x`), then `a` is a join-irreducible
> Frankl witness: `2 · |↑a| ≤ |L|`.

The proof is a clean injection `↑a → L ∖ ↑a`, `x ↦ y`: the relative complement
`y` satisfies `a ≰ y` (else `a = a ⊓ y = ⊥`), so `y ∉ ↑a`; and `x = a ⊔ y` is
recovered from `y`, so the map is injective.  Hence `|↑a| ≤ |L| − |↑a|`.

The hypothesis `hrc` holds for **relatively complemented** lattices — in
particular for **geometric** lattices (atomistic + upper-semimodular = lattices
of flats of a simple matroid), which are relatively complemented.  Naming the
"geometric lattice" instance would require a semimodular/geometric-lattice class,
absent from Mathlib `v4.28.0`; the relative-complement hypothesis here captures
the operative content directly and also covers complemented modular lattices
(subspace lattices) and any relatively complemented lattice.
-/

set_option autoImplicit false

namespace Frankl

variable {L : Type*} [Lattice L] [OrderBot L]

/-- An atom is join-irreducible. -/
theorem supIrred_of_isAtom {a : L} (ha : IsAtom a) : SupIrred a := by
  refine ⟨fun h => ha.1 (le_bot_iff.mp (h bot_le)), ?_⟩
  intro b c hbc
  by_cases hb : b = a
  · exact Or.inl hb
  · have hba : b < a := lt_of_le_of_ne (le_sup_left.trans hbc.le) hb
    rw [ha.2 b hba, bot_sup_eq] at hbc
    exact Or.inr hbc

/-- **Relative-complement atom witness.**  If `a` is an atom of a finite lattice
and every element above `a` has a relative complement of `a` below it, then `a`
is a join-irreducible lying below at most half the lattice — a Frankl witness.

This is the elementary core of the geometric-lattice case (geometric lattices are
relatively complemented).  No semimodularity is used. -/
theorem franklLattice_witness_of_atom_relComplemented [Finite L] {a : L}
    (ha : IsAtom a) (hrc : ∀ x : L, a ≤ x → ∃ y : L, a ⊓ y = ⊥ ∧ a ⊔ y = x) :
    SupIrred a ∧ 2 * Nat.card {x : L // a ≤ x} ≤ Nat.card L := by
  refine ⟨supIrred_of_isAtom ha, ?_⟩
  classical
  -- the chosen relative complement of `a` below `x` is not `≥ a`
  have hmem : ∀ x : {x : L // a ≤ x}, ¬ a ≤ (hrc x.1 x.2).choose := by
    intro x hay
    have h1 := (hrc x.1 x.2).choose_spec.1
    rw [inf_eq_left.mpr hay] at h1
    exact ha.1 h1
  -- `x ↦ (relative complement)` injects `↑a` into its complement, since `x = a ⊔ y`
  have hf : Function.Injective
      (fun x : {x : L // a ≤ x} =>
        (⟨(hrc x.1 x.2).choose, hmem x⟩ : {z : L // ¬ a ≤ z})) := by
    intro x x' hxx'
    have e : (hrc x.1 x.2).choose = (hrc x'.1 x'.2).choose := congrArg Subtype.val hxx'
    apply Subtype.ext
    have h2 := (hrc x.1 x.2).choose_spec.2
    have h2' := (hrc x'.1 x'.2).choose_spec.2
    rw [← h2, ← h2', e]
  have hinj : Nat.card {x : L // a ≤ x} ≤ Nat.card {z : L // ¬ a ≤ z} :=
    Nat.card_le_card_of_injective _ hf
  have hsum : Nat.card {x : L // a ≤ x} + Nat.card {z : L // ¬ a ≤ z} = Nat.card L := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun x => a ≤ x))
  omega

/-- **Concrete instantiation: complemented modular lattices.**  A complemented
modular lattice is relatively complemented (Mathlib's `exists_disjoint_and_sup_eq`),
so every atom is a Frankl witness.  This validates the mechanism on a genuine
Mathlib class (e.g. subspace lattices of a finite-dimensional vector space); it is
subsumed by `franklLattice_of_modular` but gives the sharper information that an
*atom* is the witness.  The genuinely new geometric (non-modular semimodular)
case — e.g. partition lattices — is *not* reachable this way: it needs a
semimodular/geometric-lattice class, which Mathlib `v4.28.0` lacks. -/
theorem franklLattice_witness_of_atom_complementedModular
    {L : Type*} [Lattice L] [BoundedOrder L] [IsModularLattice L]
    [ComplementedLattice L] [Finite L] {a : L} (ha : IsAtom a) :
    SupIrred a ∧ 2 * Nat.card {x : L // a ≤ x} ≤ Nat.card L := by
  refine franklLattice_witness_of_atom_relComplemented ha (fun x hax => ?_)
  obtain ⟨y, hdis, hsup⟩ := IsModularLattice.exists_disjoint_and_sup_eq hax
  exact ⟨y, disjoint_iff.mp hdis, hsup⟩

end Frankl
