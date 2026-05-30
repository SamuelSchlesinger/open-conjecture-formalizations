import OneThirdTwoThirds.Basic

/-!
# The 1/3–2/3 conjecture — incomparable pairs split nontrivially

This file proves the baseline fact underlying the whole problem: for an
incomparable pair `x ∥ y`, *both* orders are realized by some linear extension,
so

```
0 < e(P, x<y) < e(P),   i.e.   δ(x,y) ∈ (0,1).
```

(For a *comparable* pair `x < y` every extension puts `x` before `y`, so
`δ = 1`; incomparability is exactly the regime where the conjecture's `[1/3,2/3]`
window is meaningful.)

## Technique: augment, then extend

To exhibit a linear extension placing `x` before `y`, augment the order with the
single relation `x < y`:

```
a ≤' b  :⟺  a ≤ b  ∨  (a ≤ x ∧ y ≤ b).
```

`≤'` is again a partial order — the only way it could fail antisymmetry is a
chain `y ≤ … ≤ x`, which would force `y ≤ x`, contradicting incomparability.
Since `≤'` is a finite partial order it has a linear extension
(`numLinExts_pos`), and any `≤'`-linear-extension is a `≤`-linear-extension
(because `≤ ⊆ ≤'`) that places `x` before `y` (because `x ≤' y`).  This is the
same "augment a poset with one forced relation" move that drives the
deletion/contraction arguments in the literature.

Everything here is `sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

section Helper
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- For any finite decidable partial order given as a *relation* `le'`, and any
forced strict relation `le' x y` with `x ≠ y`, there is a ranking (monotone
injection to `Fin |X|`) realizing `le'` that places `x` strictly before `y`.

This packages the "augment-and-extend" construction with `le'` as the *sole*
order on `X`, so it composes cleanly when the caller already carries a different
ambient `PartialOrder`. -/
theorem exists_ranking_with_lt (le' : X → X → Prop) [DecidableRel le']
    (hrefl : ∀ a, le' a a)
    (htrans : ∀ a b c, le' a b → le' b c → le' a c)
    (hantisymm : ∀ a b, le' a b → le' b a → a = b)
    {x y : X} (hxy : le' x y) (hne : x ≠ y) :
    ∃ f : X → Fin (Fintype.card X),
      Function.Injective f ∧ (∀ a b, le' a b → f a ≤ f b) ∧ f x < f y := by
  letI po : PartialOrder X :=
    { le := le'
      lt := fun a b => le' a b ∧ ¬ le' b a
      le_refl := hrefl
      le_trans := htrans
      le_antisymm := hantisymm
      lt_iff_le_not_ge := fun _ _ => Iff.rfl }
  haveI : DecidableLE X := fun a b => (inferInstance : Decidable (le' a b))
  obtain ⟨f, hf⟩ := Finset.card_pos.mp (numLinExts_pos (X := X))
  rw [mem_linExts] at hf
  obtain ⟨hinj, hmono⟩ := hf
  refine ⟨f, hinj, hmono, ?_⟩
  exact lt_of_le_of_ne (hmono x y hxy) (fun heq => hne (hinj heq))

end Helper

variable {X : Type*} [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]

/-- **An incomparable pair is realized in the `x < y` order by some linear
extension**: `0 < e(P, x<y)`.

We apply `exists_ranking_with_lt` to the augmented partial order `≤'` (with
`x < y` forced); the resulting ranking is a linear extension of `P` (since
`≤ ⊆ ≤'`) that puts `x` before `y`. -/
theorem numBefore_pos_of_incomp {x y : X} (h : Incomp x y) : 0 < numBefore x y := by
  classical
  -- the augmented relation `≤'`
  let r' : X → X → Prop := fun a b => a ≤ b ∨ (a ≤ x ∧ y ≤ b)
  have hyx : ¬ y ≤ x := h.2
  haveI : DecidableRel r' := fun a b => (inferInstance : Decidable (a ≤ b ∨ (a ≤ x ∧ y ≤ b)))
  obtain ⟨f, hinj, hmono, hlt⟩ :=
    exists_ranking_with_lt r'
      (fun a => Or.inl le_rfl)
      (by
        intro a b c hab hbc
        rcases hab with hab | ⟨hax, hyb⟩ <;> rcases hbc with hbc | ⟨hbx, hyc⟩
        · exact Or.inl (hab.trans hbc)
        · exact Or.inr ⟨hab.trans hbx, hyc⟩
        · exact Or.inr ⟨hax, hyb.trans hbc⟩
        · exact Or.inr ⟨hax, hyc⟩)
      (by
        intro a b hab hba
        rcases hab with hab | ⟨hax, hyb⟩ <;> rcases hba with hba | ⟨hbx, hya⟩
        · exact le_antisymm hab hba
        · exact absurd (hya.trans (hab.trans hbx)) hyx
        · exact absurd ((hyb.trans hba).trans hax) hyx
        · exact absurd (hyb.trans hbx) hyx)
      (Or.inr ⟨le_rfl, le_rfl⟩) h.ne
  -- `f` is a linear extension of `P` (since `≤ ⊆ ≤'`) placing `x` before `y`
  refine Finset.card_pos.mpr ⟨f, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨mem_linExts.mpr ⟨hinj, fun a b hab => hmono a b (Or.inl hab)⟩, hlt⟩

/-- The dual statement: `e(P, x<y) < e(P)` for an incomparable pair, since the
opposite order `y < x` is also realized. -/
theorem numBefore_lt_numLinExts_of_incomp {x y : X} (h : Incomp x y) :
    numBefore x y < numLinExts (X := X) := by
  have hpart := numBefore_add_numBefore x y h.ne
  have hpos := numBefore_pos_of_incomp h.symm
  omega

/-- **`δ(x,y) ∈ (0,1)` for every incomparable pair** (fraction-free): both
before-counts are strictly between `0` and `e(P)`. -/
theorem numBefore_pos_lt {x y : X} (h : Incomp x y) :
    0 < numBefore x y ∧ numBefore x y < numLinExts (X := X) :=
  ⟨numBefore_pos_of_incomp h, numBefore_lt_numLinExts_of_incomp h⟩

end OneThirdTwoThirds
