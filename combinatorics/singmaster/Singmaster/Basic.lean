import Singmaster.Defs

/-!
# Singmaster's conjecture — counting infrastructure

This file establishes:

* `self_le_choose` — the row-minimum bound `n ≤ C(n,k)` for `0 < k < n`
  (binomials away from the `1`-valued ends are at least `n`).
* `le_of_choose_eq` — **completeness of the search box**: every occurrence of
  `a ≥ 2` has `n ≤ a`, so `singmasterCount` is the *true* Pascal multiplicity.
* `two_le_singmasterCount` — the trivial lower bound: every `a ≥ 3` appears at
  least twice (`a = C(a,1) = C(a,a-1)`), so any Singmaster constant is `≥ 2`.

All results are `sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace Singmaster

/-- Auxiliary monotonicity: for `1 ≤ k ≤ n/2`, `n ≤ C(n,k)`.  Binomials increase
from `C(n,1) = n` up to the middle. -/
theorem self_le_choose_aux (n : ℕ) :
    ∀ k, 1 ≤ k → k ≤ n / 2 → n ≤ n.choose k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hk
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; exact le_of_eq (Nat.choose_one_right n).symm
    · have hstep : n.choose m ≤ n.choose (m + 1) :=
        Nat.choose_le_succ_of_lt_half_left (by omega)
      exact (ih hm (by omega)).trans hstep

/-- **Row-minimum bound.**  Away from the `1`-valued ends, every binomial
coefficient is at least `n`: `n ≤ C(n,k)` for `0 < k < n`. -/
theorem self_le_choose {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) : n ≤ n.choose k := by
  rcases le_or_gt k (n / 2) with h | h
  · exact self_le_choose_aux n k hk0 h
  · rw [← Nat.choose_symm hkn.le]
    exact self_le_choose_aux n (n - k) (by omega) (by omega)

/-- **Completeness of the search box.**  Any occurrence of `a ≥ 2` in Pascal's
triangle has `n ≤ a`; hence `singmasterCount a` (the count over `{0,…,a}²`)
equals the true multiplicity of `a`. -/
theorem le_of_choose_eq {a n k : ℕ} (ha : 2 ≤ a) (hkn : k ≤ n) (h : n.choose k = a) :
    n ≤ a := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; rw [Nat.choose_zero_right] at h; omega
  · rcases eq_or_lt_of_le hkn with hkeq | hklt
    · subst hkeq; rw [Nat.choose_self] at h; omega
    · have := self_le_choose hk0 hklt; omega

/-- `a = C(a,1)`, so for `a ≥ 2` the pair `(a,1)` is an occurrence. -/
theorem mem_occurrences_a_one {a : ℕ} (ha : 2 ≤ a) : (a, 1) ∈ occurrences a := by
  rw [mem_occurrences]
  exact ⟨⟨by omega, by omega⟩, by omega, Nat.choose_one_right a⟩

/-- `a = C(a,a-1)`, so for `a ≥ 3` the pair `(a, a-1)` is a *second* occurrence. -/
theorem mem_occurrences_a_pred {a : ℕ} (ha : 3 ≤ a) : (a, a - 1) ∈ occurrences a := by
  rw [mem_occurrences]
  refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
  rw [Nat.choose_symm (by omega : 1 ≤ a), Nat.choose_one_right]

/-- **Every `a ≥ 3` appears at least twice** in Pascal's triangle: it equals
both `C(a,1)` and `C(a,a-1)`, and these are distinct positions.  Hence any
Singmaster constant must be `≥ 2`. -/
theorem two_le_singmasterCount {a : ℕ} (ha : 3 ≤ a) : 2 ≤ singmasterCount a := by
  have hsub : ({(a, 1), (a, a - 1)} : Finset (ℕ × ℕ)) ⊆ occurrences a := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h <;> subst h
    · exact mem_occurrences_a_one (by omega)
    · exact mem_occurrences_a_pred ha
  have hne : ((a, 1) : ℕ × ℕ) ≠ (a, a - 1) := by
    intro h; rw [Prod.mk.injEq] at h; omega
  have hcard : ({(a, 1), (a, a - 1)} : Finset (ℕ × ℕ)).card = 2 := Finset.card_pair hne
  calc 2 = ({(a, 1), (a, a - 1)} : Finset (ℕ × ℕ)).card := hcard.symm
    _ ≤ (occurrences a).card := Finset.card_le_card hsub
    _ = singmasterCount a := rfl

end Singmaster
