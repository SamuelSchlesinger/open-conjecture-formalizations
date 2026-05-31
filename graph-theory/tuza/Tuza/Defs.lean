import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice

/-!
# Tuza's conjecture — definitions

Reference: https://en.wikipedia.org/wiki/Tuza%27s_conjecture

For a finite simple graph `G`:

* a **triangle** is a 3-element clique;
* its three **edges** are its 2-element subsets;
* a **triangle packing** is a set of pairwise *edge-disjoint* triangles, and
  `ν(G)` is the largest size of one;
* a **triangle edge cover** is a set of edges meeting every triangle (deleting
  them makes `G` triangle-free), and `τ(G)` is the smallest size of one.

> **Conjecture (Zs. Tuza, 1981).** `τ(G) ≤ 2·ν(G)` for every finite graph `G`.

The trivial bounds `ν(G) ≤ τ(G) ≤ 3·ν(G)` are proved in `Basic`/`Bounds`; the
factor `2` is the open problem (and is best possible — `K₄` has `τ = 2`, `ν = 1`).

## Modeling

We keep everything inside `Finset V`: a triangle and an edge are both finite
vertex sets (a 3-clique and a 2-clique), so the edges of a triangle `t` are
exactly `t.powersetCard 2`.  `ν` and `τ` are defined as `sSup`/`sInf` over the
sets of achievable packing/cover sizes — no decidability instances required.
-/

set_option autoImplicit false

namespace Tuza

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The triangles of `G`: its 3-element cliques. -/
def triangles : Finset (Finset V) := G.cliqueFinset 3

/-- The edges of `G`: its 2-element cliques (each an edge as a vertex pair). -/
def edges : Finset (Finset V) := G.cliqueFinset 2

/-- The three edges of a triangle `t`: its 2-element subsets. -/
def triEdges (t : Finset V) : Finset (Finset V) := t.powersetCard 2

/-- A **triangle packing**: a set of triangles that are pairwise edge-disjoint
(no two share an edge). -/
def IsPacking (P : Finset (Finset V)) : Prop :=
  P ⊆ triangles G ∧
    ∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint (triEdges t₁) (triEdges t₂)

/-- A **triangle edge cover**: a set of edges meeting every triangle. -/
def IsCover (F : Finset (Finset V)) : Prop :=
  F ⊆ edges G ∧ ∀ t ∈ triangles G, ∃ e ∈ F, e ∈ triEdges t

/-- `ν(G)`: the maximum size of an edge-disjoint triangle packing. -/
noncomputable def nu : ℕ := sSup {n | ∃ P, IsPacking G P ∧ P.card = n}

/-- `τ(G)`: the minimum size of a triangle edge cover. -/
noncomputable def tau : ℕ := sInf {n | ∃ F, IsCover G F ∧ F.card = n}

/-- **Tuza's conjecture**: `τ(G) ≤ 2·ν(G)` for every finite graph. -/
def TuzaConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    tau G ≤ 2 * nu G

end Tuza
