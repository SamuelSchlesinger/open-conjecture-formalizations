import OneThirdTwoThirds.Defs

/-!
# The 1/3–2/3 conjecture — headline statement

This module states the conjecture itself.  Per the project convention (mirroring
the Frankl scaffold) the open conjecture is recorded as a single, intentional
`sorry`; every other result in the project is `sorry`-free and axiom-clean.

The conjecture is **open** (Kislitsyn 1968; Fredman; Linial 1984).  The best
known general lower bound is `δ(P) ≥ (5 − √5)/10 ≈ 0.2764`
(Brightwell–Felsner–Trotter 1995); the gap to `1/3 ≈ 0.3333` is the open
problem.  See `SmallCases.V3_balance_tight` for Linial's proof that the
constant `1/3` is best possible.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

/-- **The 1/3–2/3 conjecture.**  Every finite poset that is not a chain has an
incomparable pair `{x, y}` with `1/3 ≤ e(P, x<y)/e(P) ≤ 2/3`.

Open since Kislitsyn (1968); this is the single intentional `sorry` of the
project. -/
theorem oneThirdTwoThirds_conjecture : OneThirdTwoThirdsConjecture := by
  intro X _ _ _ _
  sorry

/-- Expanded, instance-explicit form of `oneThirdTwoThirds_conjecture`. -/
theorem oneThirdTwoThirds_conjecture_expanded :
    ∀ (X : Type) [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X],
      IsNotChain (X := X) → ∃ x y : X, IsBalancedPair x y :=
  oneThirdTwoThirds_conjecture

end OneThirdTwoThirds
