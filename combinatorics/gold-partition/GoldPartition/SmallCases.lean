import GoldPartition.Basic
import Mathlib.Tactic

namespace GoldPartition

theorem notChainRel_fin_zero_false (r : Fin 0 → Fin 0 → Prop) : ¬NotChainRel r := by
  intro h
  rcases h with ⟨a, _, _, _, _⟩
  exact Fin.elim0 a

theorem notChainRel_fin_one_false (r : Fin 1 → Fin 1 → Prop) : ¬NotChainRel r := by
  intro h
  rcases h with ⟨a, b, hab, _, _⟩
  fin_cases a
  fin_cases b
  exact hab rfl

theorem goldPartitionConjecture_fin_zero :
    ∀ r : Fin 0 → Fin 0 → Prop, (dr : DecidableRel r) →
      IsFinitePosetRel r → NotChainRel r →
      ∃ plan : TwoStepPlan 0, @GoldPartitionWitness 0 r plan dr := by
  intro r dr _ hnc
  exact (notChainRel_fin_zero_false r hnc).elim

theorem goldPartitionConjecture_fin_one :
    ∀ r : Fin 1 → Fin 1 → Prop, (dr : DecidableRel r) →
      IsFinitePosetRel r → NotChainRel r →
      ∃ plan : TwoStepPlan 1, @GoldPartitionWitness 1 r plan dr := by
  intro r dr _ hnc
  exact (notChainRel_fin_one_false r hnc).elim

end GoldPartition
