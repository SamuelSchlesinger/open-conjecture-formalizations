import Tuza.Bounds

/-!
# Tuza's conjecture — the edge-disjoint case `τ = ν`

If the triangles of `G` are pairwise **edge-disjoint** (a "linear" triangle
hypergraph — no two triangles share an edge), then packing and covering coincide:

```
ν(G) = τ(G) = (number of triangles).
```

Indeed the whole set of triangles is then a packing, so `ν = #triangles`; and
picking one edge from each triangle gives a cover of `#triangles` edges, so
`τ ≤ #triangles = ν`, while `ν ≤ τ` always.  In particular `τ ≤ 2ν` holds with
room to spare — a clean sub-case of Tuza's conjecture.

(This is the opposite extreme to the tight `K₄`, where all triangles pairwise
*share* edges.)  `sorry`-free.
-/

set_option autoImplicit false

namespace Tuza

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The triangles of `G` are pairwise edge-disjoint. -/
def IsTriangleEdgeDisjoint : Prop :=
  ∀ t₁ ∈ triangles G, ∀ t₂ ∈ triangles G, t₁ ≠ t₂ → Disjoint (triEdges t₁) (triEdges t₂)

/-- When triangles are edge-disjoint, the whole triangle set is a maximum
packing, so `ν(G)` equals the number of triangles. -/
theorem nu_eq_card_triangles (h : IsTriangleEdgeDisjoint G) :
    nu G = (triangles G).card := by
  apply le_antisymm
  · apply csSup_le (packing_sizes_nonempty G)
    rintro m ⟨P, hP, rfl⟩
    exact Finset.card_le_card hP.1
  · exact le_nu_of_isPacking G ⟨Finset.Subset.refl _, h⟩

/-- When triangles are edge-disjoint, choosing one edge per triangle yields a
cover, so `τ(G) ≤ ν(G)`. -/
theorem tau_le_nu_of_edgeDisjoint (h : IsTriangleEdgeDisjoint G) : tau G ≤ nu G := by
  classical
  -- pick an edge in each triangle
  set e : Finset V → Finset V :=
    fun t => if hne : (triEdges t).Nonempty then hne.choose else ∅ with he_def
  have hmem : ∀ t ∈ triangles G, e t ∈ triEdges t := by
    intro t ht
    have hne := triEdges_nonempty G ht
    simp only [he_def, dif_pos hne]
    exact hne.choose_spec
  set F := (triangles G).image e with hF_def
  have hcover : IsCover G F := by
    refine ⟨?_, fun t ht => ⟨e t, Finset.mem_image_of_mem e ht, hmem t ht⟩⟩
    intro x hx
    rw [hF_def, Finset.mem_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact triEdges_subset_edges G ht (hmem t ht)
  calc tau G ≤ F.card := tau_le_of_isCover G hcover
    _ ≤ (triangles G).card := Finset.card_image_le
    _ = nu G := (nu_eq_card_triangles G h).symm

/-- **The edge-disjoint case: `τ(G) = ν(G)`.** -/
theorem tau_eq_nu_of_edgeDisjoint (h : IsTriangleEdgeDisjoint G) : tau G = nu G :=
  le_antisymm (tau_le_nu_of_edgeDisjoint G h) (nu_le_tau G)

/-- Tuza's conjecture holds (with room to spare) when the triangles are
edge-disjoint. -/
theorem tuza_of_edgeDisjoint (h : IsTriangleEdgeDisjoint G) : tau G ≤ 2 * nu G := by
  rw [tau_eq_nu_of_edgeDisjoint G h]; omega

end Tuza
