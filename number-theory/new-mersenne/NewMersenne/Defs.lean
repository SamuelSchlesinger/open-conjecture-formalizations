import Mathlib.Data.Nat.Prime.Basic

namespace NewMersenne

/-- First New Mersenne shape condition: `p + 1` is a power of `2`. -/
def ShapeA (p : Nat) : Prop :=
  ∃ k : Nat, p + 1 = 2 ^ k

/-- Second New Mersenne shape condition: `p` is one more than a power of `2`. -/
def ShapeB (p : Nat) : Prop :=
  ∃ k : Nat, p = 2 ^ k + 1

/-- Third New Mersenne shape condition: `p + 3` is a power of `4`. -/
def ShapeC (p : Nat) : Prop :=
  ∃ k : Nat, p + 3 = 4 ^ k

/-- Fourth New Mersenne shape condition: `p` is three more than a power of `4`. -/
def ShapeD (p : Nat) : Prop :=
  ∃ k : Nat, p = 4 ^ k + 3

/-- The "special shape" condition appearing in the New Mersenne conjecture. -/
def InNewMersenneShape (p : Nat) : Prop :=
  ShapeA p ∨ ShapeB p ∨ ShapeC p ∨ ShapeD p

/-- Condition that `2^p - 1` is prime (a Mersenne prime with exponent `p`). -/
def IsMersennePrimeExponent (p : Nat) : Prop :=
  Nat.Prime (2 ^ p - 1)

/-- Decidability of the Mersenne-prime exponent predicate. -/
instance (p : Nat) : Decidable (IsMersennePrimeExponent p) := by
  unfold IsMersennePrimeExponent
  infer_instance

/-- Condition that `(2^p + 1) / 3` is prime and is integrally defined via
the divisibility side condition. -/
def IsWagstaffPrimeExponent (p : Nat) : Prop :=
  3 ∣ (2 ^ p + 1) ∧ Nat.Prime ((2 ^ p + 1) / 3)

/-- Decidability of the Wagstaff-prime exponent predicate. -/
instance (p : Nat) : Decidable (IsWagstaffPrimeExponent p) := by
  unfold IsWagstaffPrimeExponent
  infer_instance

/-- The New Mersenne conjecture:
for odd `p`, any two of
1) special shape, 2) Mersenne-prime exponent, 3) Wagstaff-prime exponent
imply the third. -/
def NewMersenneConjecture : Prop :=
  ∀ p : Nat, Odd p →
    ((InNewMersenneShape p ∧ IsMersennePrimeExponent p) → IsWagstaffPrimeExponent p) ∧
    ((InNewMersenneShape p ∧ IsWagstaffPrimeExponent p) → IsMersennePrimeExponent p) ∧
    ((IsMersennePrimeExponent p ∧ IsWagstaffPrimeExponent p) → InNewMersenneShape p)

end NewMersenne
