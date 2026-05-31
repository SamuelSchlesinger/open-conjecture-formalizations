import Singmaster.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Singmaster's conjecture — an infinite family appearing ≥ 4 times

The computational exploration found that `C(n,2)` (for `n ≥ 5`) always appears
at least four times in Pascal's triangle.  This file proves it analytically: for
`a = C(n,2)` with `n ≥ 5`, the four positions

```
(n, 2), (n, n-2), (a, 1), (a, a-1)
```

are pairwise distinct occurrences of `a` (the first two by the row identity
`C(n,2) = C(n,n-2)`; the last two by `a = C(a,1) = C(a,a-1)`; and `n < a` keeps
the two groups apart).  Hence `singmasterCount (C(n,2)) ≥ 4` for all `n ≥ 5`.

**Consequence.**  Infinitely many integers appear at least `4` times, so any
Singmaster constant `C` necessarily satisfies `C ≥ 4`.  (The known record is
`8`, attained at `3003`; an infinite family appearing `≥ 6` times exists via a
Fibonacci identity of Singmaster, not formalized here.)

`sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace Singmaster

/-- For `n ≥ 5`, `n < C(n,2)`: the triangular number `n(n-1)/2` exceeds `n`. -/
theorem self_lt_choose_two {n : ℕ} (hn : 5 ≤ n) : n < n.choose 2 := by
  rw [Nat.choose_two_right]
  have h1 : n * 4 ≤ n * (n - 1) := by
    apply Nat.mul_le_mul_left
    omega
  have h2 : n * 4 / 2 ≤ n * (n - 1) / 2 := Nat.div_le_div_right h1
  have h3 : n * 4 / 2 = n * 2 := by omega
  omega

/-- **An infinite family appearing at least four times.**  For every `n ≥ 5`,
the binomial coefficient `C(n,2)` occurs at least four times in Pascal's
triangle.  Consequently any Singmaster bound is `≥ 4`. -/
theorem four_le_singmasterCount_choose_two {n : ℕ} (hn : 5 ≤ n) :
    4 ≤ singmasterCount (n.choose 2) := by
  set a := n.choose 2 with ha_def
  have hna : n < a := self_lt_choose_two hn
  have ha6 : 6 ≤ a := by omega
  -- the row identity `C(n, n-2) = C(n, 2)`
  have hsymm : n.choose (n - 2) = a := by
    rw [ha_def, Nat.choose_symm (by omega : 2 ≤ n)]
  -- the four positions are occurrences of `a`
  have hsub : ({(n, 2), (n, n - 2), (a, 1), (a, a - 1)} : Finset (ℕ × ℕ)) ⊆ occurrences a := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h | h | h <;> subst h <;> rw [mem_occurrences]
    · exact ⟨⟨by omega, by omega⟩, by omega, ha_def.symm⟩
    · exact ⟨⟨by omega, by omega⟩, by omega, hsymm⟩
    · exact ⟨⟨by omega, by omega⟩, by omega, Nat.choose_one_right a⟩
    · refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
      rw [Nat.choose_symm (by omega : 1 ≤ a), Nat.choose_one_right]
  -- the four positions are pairwise distinct (n < a separates the two groups)
  have hcard : ({(n, 2), (n, n - 2), (a, 1), (a, a - 1)} : Finset (ℕ × ℕ)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_singleton]
  calc 4 = ({(n, 2), (n, n - 2), (a, 1), (a, a - 1)} : Finset (ℕ × ℕ)).card := hcard.symm
    _ ≤ (occurrences a).card := Finset.card_le_card hsub
    _ = singmasterCount a := rfl

/-- The Singmaster bound, if it exists, is at least `4`: no constant below `4`
can dominate every multiplicity. -/
theorem four_le_of_singmasterConjecture {C : ℕ}
    (hC : ∀ a : ℕ, 2 ≤ a → singmasterCount a ≤ C) : 4 ≤ C :=
  le_trans (four_le_singmasterCount_choose_two (le_refl 5))
    (hC ((5).choose 2) (by decide))

end Singmaster
