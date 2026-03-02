import GoldPartition.Defs

namespace GoldPartition

theorem extensionCount_nonneg {n : Nat} (r : Fin n → Fin n → Prop) [DecidableRel r] :
    0 ≤ extensionCount r := by
  exact Nat.zero_le _

theorem extensionCountWithOutcomes_nonneg {n : Nat} (r : Fin n → Fin n → Prop)
    (outs : List (Comparison n × Bool)) [DecidableRel r] :
    0 ≤ extensionCountWithOutcomes r outs := by
  exact Nat.zero_le _

/-- The equality relation on `Fin n` as a canonical finite poset relation. -/
def eqRel (n : Nat) : Fin n → Fin n → Prop := fun a b => a = b

theorem isFinitePosetRel_eqRel (n : Nat) : IsFinitePosetRel (eqRel n) := by
  constructor
  · intro a
    rfl
  constructor
  · intro a b c hab hbc
    exact hab.trans hbc
  · intro a b hab hba
    exact hab

theorem isLinearExtension_eqRel {n : Nat} (σ : Equiv.Perm (Fin n)) :
    IsLinearExtension (eqRel n) σ := by
  intro a b hab
  subst hab
  exact le_rfl

end GoldPartition
