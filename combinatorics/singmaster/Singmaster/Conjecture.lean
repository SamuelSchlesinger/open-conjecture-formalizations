import Singmaster.Defs

/-!
# Singmaster's conjecture — headline statement

Per the project convention (mirroring the Frankl / 1-3-2-3 scaffolds), the open
conjecture is recorded as a single, intentional `sorry`; every other result in
the project is `sorry`-free and axiom-clean.

The conjecture is **open** (Singmaster 1971).  The best known upper bound on the
multiplicity is `O(log a / log log a)` (Singmaster 1971; refined by
Abbott–Erdős–Hanson) — no *constant* bound is proved, which is exactly the open
problem.  Lower bound: `Family.four_le_of_singmasterConjecture` shows any
constant must be `≥ 4`, and the record `8` is attained at `3003`.
-/

set_option autoImplicit false

namespace Singmaster

/-- **Singmaster's conjecture.**  There is a constant `C` such that every integer
`a ≥ 2` occurs at most `C` times in Pascal's triangle.

Open since Singmaster (1971); this is the single intentional `sorry` of the
project. -/
theorem singmaster_conjecture : SingmasterConjecture := by
  sorry

/-- Expanded form of `singmaster_conjecture`. -/
theorem singmaster_conjecture_expanded :
    ∃ C : ℕ, ∀ a : ℕ, 2 ≤ a → singmasterCount a ≤ C :=
  singmaster_conjecture

end Singmaster
