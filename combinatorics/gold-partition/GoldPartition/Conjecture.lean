import GoldPartition.Defs

namespace GoldPartition

/-- Gold partition conjecture (two-comparison form). -/
theorem goldPartition_conjecture : GoldPartitionConjecture := by
  intro n r dr hpos hnc
  sorry

/-- Expanded form of `goldPartition_conjecture`. -/
theorem goldPartition_conjecture_expanded :
    ∀ n : Nat, ∀ r : Fin n → Fin n → Prop,
      (dr : DecidableRel r) →
      IsFinitePosetRel r → NotChainRel r →
      ∃ plan : TwoStepPlan n, @GoldPartitionWitness n r plan dr := by
  exact goldPartition_conjecture

end GoldPartition
