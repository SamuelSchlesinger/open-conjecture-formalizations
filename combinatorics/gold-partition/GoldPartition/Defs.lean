import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace GoldPartition

/-- A finite-poset relation on `Fin n` (as axioms on a binary relation). -/
def IsFinitePosetRel {n : Nat} (r : Fin n → Fin n → Prop) : Prop :=
  (∀ a : Fin n, r a a) ∧
  (∀ a b c : Fin n, r a b → r b c → r a c) ∧
  (∀ a b : Fin n, r a b → r b a → a = b)

/-- Total comparability (chain condition) for a relation on `Fin n`. -/
def IsChainRel {n : Nat} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ a b : Fin n, r a b ∨ r b a

/-- Existence of an incomparable pair of distinct elements. -/
def NotChainRel {n : Nat} (r : Fin n → Fin n → Prop) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧ ¬r a b ∧ ¬r b a

/-- A permutation is a linear extension of `r` if it preserves the order:
`a ≤_r b` implies `a` appears no later than `b` in the permutation order. -/
def IsLinearExtension {n : Nat} (r : Fin n → Fin n → Prop)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b : Fin n, r a b → σ.symm a ≤ σ.symm b

/-- Number of linear extensions of `r`. -/
noncomputable def extensionCount {n : Nat} (r : Fin n → Fin n → Prop) [DecidableRel r] : Nat :=
  by
    classical
    exact Fintype.card {σ : Equiv.Perm (Fin n) // IsLinearExtension r σ}

/-- A comparison query on `Fin n`. -/
structure Comparison (n : Nat) where
  left : Fin n
  right : Fin n
  ne : left ≠ right
deriving DecidableEq

/-- An outcome says whether `left < right` (`true`) or `right < left` (`false`)
in the permutation order. -/
def SatisfiesOutcome {n : Nat} (σ : Equiv.Perm (Fin n)) (q : Comparison n) (o : Bool) : Prop :=
  if o then σ.symm q.left < σ.symm q.right else σ.symm q.right < σ.symm q.left

/-- Satisfaction of a finite list of comparison outcomes. -/
def SatisfiesOutcomes {n : Nat} (σ : Equiv.Perm (Fin n))
    (outs : List (Comparison n × Bool)) : Prop :=
  ∀ t ∈ outs, SatisfiesOutcome σ t.1 t.2

/-- Number of linear extensions satisfying additional comparison outcomes. -/
noncomputable def extensionCountWithOutcomes {n : Nat} (r : Fin n → Fin n → Prop)
    (outs : List (Comparison n × Bool)) [DecidableRel r] : Nat :=
  by
    classical
    exact Fintype.card {σ : Equiv.Perm (Fin n) //
      IsLinearExtension r σ ∧ SatisfiesOutcomes σ outs}

/-- A two-step adaptive comparison plan: second comparison may depend on the
first comparison's outcome. -/
structure TwoStepPlan (n : Nat) where
  first : Comparison n
  second : Bool → Comparison n

/-- Branch-wise Gold-partition inequality for a given relation and plan. -/
def GoldPartitionWitness {n : Nat} (r : Fin n → Fin n → Prop) (plan : TwoStepPlan n)
    [DecidableRel r] : Prop :=
  ∀ o₁ o₂ : Bool,
    extensionCount r ≥
      extensionCountWithOutcomes r [(plan.first, o₁)] +
      extensionCountWithOutcomes r [(plan.first, o₁), (plan.second o₁, o₂)]

/-- Gold partition conjecture (two-comparison form):
every finite non-chain poset admits a two-step comparison plan with the
branch-wise inequality `t₀ ≥ t₁ + t₂`. -/
def GoldPartitionConjecture : Prop :=
  ∀ n : Nat, ∀ r : Fin n → Fin n → Prop,
    (dr : DecidableRel r) →
    IsFinitePosetRel r → NotChainRel r →
      ∃ plan : TwoStepPlan n, @GoldPartitionWitness n r plan dr

end GoldPartition
