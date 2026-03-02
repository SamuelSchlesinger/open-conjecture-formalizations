import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dittert

open Matrix
open scoped BigOperators

noncomputable section

/-- The domain `K_n` in Dittert's setting:
nonnegative real `n × n` matrices with total sum `n`. -/
def InKn (n : Nat) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ (∑ i : Fin n, ∑ j : Fin n, A i j) = (n : ℝ)

/-- Product of row sums. -/
def rowSumsProduct {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ i : Fin n, ∑ j : Fin n, A i j

/-- Product of column sums. -/
def colSumsProduct {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ j : Fin n, ∑ i : Fin n, A i j

/-- Dittert's objective functional:
row-product + column-product - permanent. -/
def dittertFunctional {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  rowSumsProduct A + colSumsProduct A - Matrix.permanent A

/-- Uniform entry value used for the candidate maximizer. -/
def uniformEntry (n : Nat) : ℝ :=
  if h : n = 0 then 0 else (1 : ℝ) / (n : ℝ)

/-- Uniform matrix candidate (all entries equal). -/
def uniformMatrix (n : Nat) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => uniformEntry n

/-- Dittert conjecture at size `n`:
the uniform matrix maximizes the Dittert functional on `K_n`,
with equality only at the uniform matrix. -/
def DittertConjectureAt (n : Nat) : Prop :=
  n > 0 →
    ∀ A : Matrix (Fin n) (Fin n) ℝ, InKn n A →
      dittertFunctional A ≤ dittertFunctional (uniformMatrix n) ∧
      (dittertFunctional A = dittertFunctional (uniformMatrix n) → A = uniformMatrix n)

/-- Global Dittert conjecture over all positive matrix sizes. -/
def DittertConjecture : Prop :=
  ∀ n : Nat, DittertConjectureAt n

end

end Dittert
