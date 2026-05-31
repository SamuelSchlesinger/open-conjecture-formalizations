import Tuza.Defs

/-!
# Tuza's conjecture — headline statement

Per the project convention (mirroring the Frankl / 1-3-2-3 / Singmaster
scaffolds), the open conjecture is recorded as a single intentional `sorry`;
every other result in the project is `sorry`-free.

The conjecture is **open** (Zs. Tuza, 1981).  Known partial results: it holds for
planar graphs (Tuza 1990), for `K₄`-free graphs, for graphs with few edges, and
the fractional relaxation `τ* ≤ 2ν*` is known (Krivelevich 1995); the best
general bound is `τ ≤ 3ν` (`Bounds.tau_le_three_mul_nu`), improved to
`τ ≤ (3 − 3/23)·ν ≈ 2.87·ν` (Haxell 1999).  The constant `2` is best possible
(`Tightness.tuza_tight`, via `K₄`).
-/

set_option autoImplicit false

namespace Tuza

/-- **Tuza's conjecture** (1981): for every finite graph, the triangle edge-cover
number is at most twice the edge-disjoint triangle packing number, `τ(G) ≤ 2·ν(G)`.

Open; this is the single intentional `sorry` of the project. -/
theorem tuza_conjecture : TuzaConjecture := by
  intro V _ _ G _
  sorry

/-- Expanded form of `tuza_conjecture`. -/
theorem tuza_conjecture_expanded :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      tau G ≤ 2 * nu G :=
  tuza_conjecture

end Tuza
