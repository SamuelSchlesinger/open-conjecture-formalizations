import Fortune.Structure
import Mathlib.Data.Nat.Prime.Infinite

namespace Fortune

theorem exists_fortunateOffset (n : Nat) : ∃ m : Nat, IsFortunateOffset n m := by
  let N := nthPrimorial n
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (N + 2)
  refine ⟨p - N, ?_⟩
  have hN_le_p : N ≤ p := le_trans (Nat.le_add_right N 2) hp_ge
  have hm_ge_two : 2 ≤ p - N := by
    have hp_ge' : 2 + N ≤ p := by simpa [Nat.add_comm] using hp_ge
    exact Nat.le_sub_of_add_le hp_ge'
  constructor
  · exact lt_of_lt_of_le (by decide : 1 < 2) hm_ge_two
  · have hsum : N + (p - N) = p := Nat.add_sub_of_le hN_le_p
    simpa [N, hsum] using hp_prime

theorem exists_leastFortunateOffset (n : Nat) : ∃ m : Nat, IsLeastFortunateOffset n m := by
  classical
  let hExist : ∃ m : Nat, IsFortunateOffset n m := exists_fortunateOffset n
  refine ⟨Nat.find hExist, ?_⟩
  constructor
  · exact Nat.find_spec hExist
  · intro k hk_gt_one hk_lt_find hk_prime
    have hkOffset : IsFortunateOffset n k := ⟨hk_gt_one, hk_prime⟩
    have hfind_le_k : Nat.find hExist ≤ k := Nat.find_min' hExist hkOffset
    exact (Nat.not_le_of_lt hk_lt_find) hfind_le_k

theorem hasLeastFortunateOffset (n : Nat) : HasLeastFortunateOffset n := by
  exact exists_leastFortunateOffset n

theorem leastFortunateOffset_unique {n m₁ m₂ : Nat}
    (h₁ : IsLeastFortunateOffset n m₁) (h₂ : IsLeastFortunateOffset n m₂) :
    m₁ = m₂ := by
  have hm₁_le_m₂ : m₁ ≤ m₂ := by
    exact le_of_not_gt fun hm₂_lt_m₁ => (h₁.2 m₂ h₂.1.1 hm₂_lt_m₁ h₂.1.2).elim
  have hm₂_le_m₁ : m₂ ≤ m₁ := by
    exact le_of_not_gt fun hm₁_lt_m₂ => (h₂.2 m₁ h₁.1.1 hm₁_lt_m₂ h₁.1.2).elim
  exact le_antisymm hm₁_le_m₂ hm₂_le_m₁

theorem existsUnique_leastFortunateOffset (n : Nat) :
    ∃! m : Nat, IsLeastFortunateOffset n m := by
  obtain ⟨m, hm⟩ := exists_leastFortunateOffset n
  refine ⟨m, hm, ?_⟩
  intro k hk
  exact leastFortunateOffset_unique hk hm

end Fortune
