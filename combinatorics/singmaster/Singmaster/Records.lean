import Singmaster.Basic

/-!
# Singmaster's conjecture — the record multiplicity `N(3003) ≥ 8`

`3003` is the smallest number appearing **eight** times in Pascal's triangle —
the largest multiplicity ever observed, and the basis for Singmaster's
conjectured constant `C = 8`.  Its eight occurrences are

```
3003 = C(3003,1) = C(3003,3002)
     = C(78,2)   = C(78,76)
     = C(15,5)   = C(15,10)
     = C(14,6)   = C(14,8).
```

This file proves `8 ≤ singmasterCount 3003`, hence **`8 ≤ C`** for any Singmaster
constant (`eight_le_of_singmasterConjecture`).  Combined with
`Family.four_le_of_singmasterConjecture` and the experimental upper bound `8`,
the conjecture pins the constant to exactly `8`.

The three "small-row" identities `C(78,2) = C(15,5) = C(14,6) = 3003` are
evaluated by the kernel (`decide`); the symmetric partners use `Nat.choose_symm`;
the top row uses `Nat.choose_one_right`.  Membership is routed through the
abstract lemma `card_le_singmasterCount`, so elaboration never unfolds the
(enormous) `occurrences 3003`.  `sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace Singmaster

/-- The eight known positions of `3003` in Pascal's triangle. -/
def positions3003 : Finset (ℕ × ℕ) :=
  {(3003, 1), (3003, 3002), (78, 2), (78, 76), (15, 5), (15, 10), (14, 6), (14, 8)}

/-- **`3003` appears at least eight times in Pascal's triangle.** -/
theorem eight_le_singmasterCount_3003 : 8 ≤ singmasterCount 3003 := by
  -- the eight binomial identities (symmetric partners reduced to small `k`)
  have e1 : Nat.choose 3003 1 = 3003 := Nat.choose_one_right 3003
  have e2 : Nat.choose 3003 3002 = 3003 := by
    have h : (3002 : ℕ) = 3003 - 1 := by omega
    rw [h, Nat.choose_symm (by omega), Nat.choose_one_right]
  have e3 : Nat.choose 78 2 = 3003 := by rw [Nat.choose_two_right]
  have e4 : Nat.choose 78 76 = 3003 := by
    have h : (76 : ℕ) = 78 - 2 := by omega
    rw [h, Nat.choose_symm (by omega)]; exact e3
  have e5 : Nat.choose 15 5 = 3003 := by decide
  have e6 : Nat.choose 15 10 = 3003 := by
    have h : (10 : ℕ) = 15 - 5 := by omega
    rw [h, Nat.choose_symm (by omega)]; exact e5
  have e7 : Nat.choose 14 6 = 3003 := by decide
  have e8 : Nat.choose 14 8 = 3003 := by
    have h : (8 : ℕ) = 14 - 6 := by omega
    rw [h, Nat.choose_symm (by omega)]; exact e7
  have hcard : positions3003.card = 8 := by decide
  rw [← hcard]
  apply card_le_singmasterCount
  intro p hp
  simp only [positions3003, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h | h | h <;> subst h <;>
    refine ⟨by omega, by omega, ?_⟩
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7
  · exact e8

/-- **Any Singmaster constant is at least `8`.**  Since `3003` occurs eight times,
no bound below `8` can dominate every multiplicity.  (With the experimental
maximum of `8`, this matches Singmaster's conjectured value `C = 8`.) -/
theorem eight_le_of_singmasterConjecture {C : ℕ}
    (hC : ∀ a : ℕ, 2 ≤ a → singmasterCount a ≤ C) : 8 ≤ C :=
  le_trans eight_le_singmasterCount_3003 (hC 3003 (by omega))

end Singmaster
