import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Frankl's Union-Closed Sets Conjecture

Reference: https://doi.org/10.1016/0097-3165(92)90068-6
-/

set_option autoImplicit false

namespace Frankl

variable {α : Type*} [DecidableEq α]

/-- The union of all member-sets in a finite family. -/
def familyUnion (F : Finset (Finset α)) : Finset α :=
  F.biUnion id

/-- A finite family of finite sets is union-closed when the union of any two
member-sets is again a member-set. -/
def IsUnionClosed (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- The member-sets of `F` that contain `x`. -/
def memberSubfamily (x : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun A => x ∈ A)

/-- The member-sets of `F` that do not contain `x`. -/
def nonmemberSubfamily (x : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun A => x ∉ A)

/-- The number of member-sets of `F` containing `x`. -/
def memberCount (x : α) (F : Finset (Finset α)) : Nat :=
  (memberSubfamily x F).card

/-- The usual nontriviality hypothesis: at least one member-set is nonempty. -/
def HasNonemptyMember (F : Finset (Finset α)) : Prop :=
  ∃ A ∈ F, A.Nonempty

/-- `x` witnesses Frankl's lower bound for the family `F`.  The inequality is
written without fractions as `|F| ≤ 2 * count(x)`. -/
def IsFranklElement (x : α) (F : Finset (Finset α)) : Prop :=
  x ∈ familyUnion F ∧ F.card ≤ 2 * memberCount x F

/-- Frankl's union-closed sets conjecture for one finite family. -/
def FranklConjectureFor (F : Finset (Finset α)) : Prop :=
  IsUnionClosed F → HasNonemptyMember F → ∃ x : α, IsFranklElement x F

/-- Frankl's union-closed sets conjecture:
every nontrivial finite union-closed family has an element contained in at
least half of the member-sets. -/
def FranklConjecture : Prop :=
  ∀ {α : Type} [DecidableEq α], ∀ F : Finset (Finset α), FranklConjectureFor F

end Frankl
