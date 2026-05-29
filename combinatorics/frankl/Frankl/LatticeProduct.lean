import Frankl.Lattice

/-!
# Frankl's lattice conjecture reduces to directly-indecomposable lattices

Reference: `research/frankl_nonlocality_synthesis.md` (idea 4: structural
induction rather than a local witness-selector).

A Frankl witness in one factor of a product **lifts** to the product: if `j₁` is
a join-irreducible of `L₁` below at most half of `L₁`, then `(j₁, ⊥)` is a
join-irreducible of `L₁ × L₂` below at most half of `L₁ × L₂`.  Indeed
`↑(j₁, ⊥) ≃ ↑j₁ × L₂`, so the `½` bound is preserved factorwise.

Consequently a **nontrivial direct product is automatically a Frankl lattice**
(take a witness from either factor), and by induction on `Nat.card` the lattice
form of Frankl's conjecture reduces to the **directly-indecomposable** lattices.
This is a genuine reduction obtained *without* selecting a witness locally — the
non-locality obstruction (every local selector is conjecture-equivalent) does
not apply to a structural product argument.  In particular the Boolean lattices,
being products of two-element chains, are handled by this route entirely.
-/

set_option autoImplicit false

namespace Frankl

variable {L₁ L₂ : Type*} [Lattice L₁] [Lattice L₂]

/-- A join-irreducible witness in a factor lifts to the product: if `j₁` is
join-irreducible in `L₁`, then `(j₁, ⊥)` is join-irreducible in `L₁ × L₂`. -/
theorem supIrred_prod_bot [OrderBot L₂] {j₁ : L₁} (hj₁ : SupIrred j₁) :
    SupIrred (j₁, (⊥ : L₂)) := by
  refine ⟨?_, ?_⟩
  · -- `(j₁, ⊥)` is not a minimum, because `j₁` is not.
    intro hmin
    refine hj₁.1 (fun a ha => ?_)
    exact (hmin (Prod.mk_le_mk.mpr ⟨ha, le_rfl⟩)).1
  · -- join-irreducibility, componentwise
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    rw [Prod.mk_sup_mk, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hx2 : x₂ = ⊥ := le_bot_iff.mp (le_sup_left.trans h2.le)
    have hy2 : y₂ = ⊥ := le_bot_iff.mp (le_sup_right.trans h2.le)
    rcases hj₁.2 h1 with h | h
    · exact Or.inl (by rw [Prod.mk.injEq]; exact ⟨h, hx2⟩)
    · exact Or.inr (by rw [Prod.mk.injEq]; exact ⟨h, hy2⟩)

/-- The principal up-set of `(j₁, ⊥)` in the product is the product of the
up-set of `j₁` with all of `L₂`. -/
def upSetProdEquiv [OrderBot L₂] (j₁ : L₁) :
    {x : L₁ × L₂ // (j₁, (⊥ : L₂)) ≤ x} ≃ {a : L₁ // j₁ ≤ a} × L₂ where
  toFun := fun x => (⟨x.1.1, (Prod.mk_le_mk.mp x.2).1⟩, x.1.2)
  invFun := fun p => ⟨(p.1.1, p.2), Prod.mk_le_mk.mpr ⟨p.1.2, bot_le⟩⟩
  left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, ha⟩, b⟩; rfl

/-- **Product lemma.**  If `L₁` carries a Frankl witness (a join-irreducible
below at most half of `L₁`), then so does `L₁ × L₂`. -/
theorem franklLattice_witness_prod_left [OrderBot L₂] [Finite L₁] [Finite L₂]
    {j₁ : L₁} (hj₁ : SupIrred j₁)
    (hc : 2 * Nat.card {x : L₁ // j₁ ≤ x} ≤ Nat.card L₁) :
    ∃ j : L₁ × L₂, SupIrred j ∧
      2 * Nat.card {x : L₁ × L₂ // j ≤ x} ≤ Nat.card (L₁ × L₂) := by
  refine ⟨(j₁, ⊥), supIrred_prod_bot hj₁, ?_⟩
  rw [Nat.card_congr (upSetProdEquiv j₁), Nat.card_prod, Nat.card_prod]
  calc 2 * (Nat.card {a : L₁ // j₁ ≤ a} * Nat.card L₂)
      = (2 * Nat.card {a : L₁ // j₁ ≤ a}) * Nat.card L₂ := by ring
    _ ≤ Nat.card L₁ * Nat.card L₂ := by gcongr

/-- **Reduction to indecomposables.**  A nontrivial direct product `L₁ × L₂`
(with `L₁` having `≥ 2` elements) is a Frankl lattice as soon as `L₁` is, hence
— by induction on `Nat.card` — Frankl's lattice conjecture reduces to the
directly-indecomposable lattices.  Stated as: a Frankl witness in `L₁` yields one
in `L₁ × L₂`, with `OrderBot L₂` obtained from finiteness and nonemptiness. -/
theorem franklLattice_prod_left [Finite L₁] [Finite L₂] [Nonempty L₂]
    (h₁ : ∃ j₁ : L₁, SupIrred j₁ ∧ 2 * Nat.card {x : L₁ // j₁ ≤ x} ≤ Nat.card L₁) :
    ∃ j : L₁ × L₂, SupIrred j ∧
      2 * Nat.card {x : L₁ × L₂ // j ≤ x} ≤ Nat.card (L₁ × L₂) := by
  obtain ⟨j₁, hj₁, hc⟩ := h₁
  letI : Fintype L₂ := Fintype.ofFinite L₂
  letI : OrderBot L₂ := (Fintype.toBoundedOrder L₂).toOrderBot
  exact franklLattice_witness_prod_left hj₁ hc

end Frankl
