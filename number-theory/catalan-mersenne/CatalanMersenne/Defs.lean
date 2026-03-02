import Mathlib.Data.Nat.Prime.Basic

namespace CatalanMersenne

/-- The Catalan-Mersenne sequence:
`c_0 = 2`, `c_{n+1} = 2^{c_n} - 1`. -/
def catalanMersenne : Nat → Nat
  | 0 => 2
  | n + 1 => 2 ^ catalanMersenne n - 1

/-- Primality predicate for Catalan-Mersenne terms. -/
def IsCatalanMersennePrime (n : Nat) : Prop :=
  Nat.Prime (catalanMersenne n)

/-- Decidability of primality for Catalan-Mersenne terms. -/
instance (n : Nat) : Decidable (IsCatalanMersennePrime n) := by
  unfold IsCatalanMersennePrime
  infer_instance

/-- "Cutoff" form: initial Catalan-Mersenne terms are prime up to some index,
and all later terms are composite. This matches the historical
"prime up to a certain limit" formulation. -/
def CatalanMersenneCutoffConjecture : Prop :=
  ∃ N : Nat,
    (∀ n : Nat, n ≤ N → IsCatalanMersennePrime n) ∧
    (∀ n : Nat, N < n → ¬IsCatalanMersennePrime n)

end CatalanMersenne
