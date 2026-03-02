import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Nth

namespace Fortune

open scoped BigOperators

/-- The `i`-th prime, indexed from `0`. -/
noncomputable def nthPrime (i : Nat) : Nat :=
  Nat.nth Nat.Prime i

/-- The last prime included in the `n`-primorial product.
For `n = 0` this is defined as `nthPrime 0`. -/
noncomputable def lastIncludedPrime (n : Nat) : Nat :=
  nthPrime (n - 1)

/-- Product of the first `n` prime numbers, indexed from `0`.
For example: `nthPrimorial 0 = 1`, `nthPrimorial 1 = 2`, `nthPrimorial 2 = 6`. -/
noncomputable def nthPrimorial (n : Nat) : Nat :=
  ∏ i ∈ Finset.range n, nthPrime i

/-- `m` is a (strict) Fortunate offset for the first `n` primes if `m > 1`
and `nthPrimorial n + m` is prime. -/
def IsFortunateOffset (n m : Nat) : Prop :=
  1 < m ∧ Nat.Prime (nthPrimorial n + m)

/-- `m` is the least Fortunate offset for `n` if it is a Fortunate offset
and no smaller offset greater than `1` works. -/
def IsLeastFortunateOffset (n m : Nat) : Prop :=
  IsFortunateOffset n m ∧
  ∀ k : Nat, 1 < k → k < m → ¬Nat.Prime (nthPrimorial n + k)

/-- Existence of a least Fortunate offset for a fixed `n`. -/
def HasLeastFortunateOffset (n : Nat) : Prop :=
  ∃ m : Nat, IsLeastFortunateOffset n m

/-- Fortune's conjecture: every least Fortunate offset is prime. -/
def FortuneConjecture : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m

end Fortune
