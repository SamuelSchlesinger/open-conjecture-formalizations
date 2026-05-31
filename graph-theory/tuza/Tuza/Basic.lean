import Tuza.Defs

/-!
# Tuza's conjecture — counting infrastructure and the easy bound `ν ≤ τ`

This file proves:

* the basic facts about `triEdges` (each triangle has exactly three edges, all
  edges of `G`);
* that `ν` and `τ` are attained (a maximum packing and a minimum cover exist);
* the **easy direction** `ν(G) ≤ τ(G)`: in any cover, the edge-disjoint
  triangles of a packing use distinct edges, so a packing is no larger than a
  cover.

All results are `sorry`-free.
-/

set_option autoImplicit false

namespace Tuza

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem mem_triangles_iff {t : Finset V} : t ∈ triangles G ↔ G.IsNClique 3 t :=
  SimpleGraph.mem_cliqueFinset_iff

theorem mem_edges_iff {e : Finset V} : e ∈ edges G ↔ G.IsNClique 2 e :=
  SimpleGraph.mem_cliqueFinset_iff

/-- Every edge of a triangle is an edge of `G`. -/
theorem triEdges_subset_edges {t : Finset V} (ht : t ∈ triangles G) :
    triEdges t ⊆ edges G := by
  intro e he
  rw [triEdges, Finset.mem_powersetCard] at he
  rw [mem_triangles_iff] at ht
  rw [mem_edges_iff]
  exact ⟨SimpleGraph.IsClique.subset (Finset.coe_subset.mpr he.1) ht.isClique, he.2⟩

/-- A triangle has exactly three edges. -/
theorem triEdges_card {t : Finset V} (ht : t ∈ triangles G) : (triEdges t).card = 3 := by
  have h3 := ((mem_triangles_iff G).mp ht).card_eq
  rw [triEdges, Finset.card_powersetCard, h3]
  decide

theorem triEdges_nonempty {t : Finset V} (ht : t ∈ triangles G) : (triEdges t).Nonempty := by
  rw [← Finset.card_pos, triEdges_card G ht]
  decide

/-! ### The numbers `ν` and `τ` are attained -/

theorem isCover_edges : IsCover G (edges G) := by
  refine ⟨Finset.Subset.refl _, fun t ht => ?_⟩
  obtain ⟨e, he⟩ := triEdges_nonempty G ht
  exact ⟨e, triEdges_subset_edges G ht he, he⟩

theorem cover_sizes_nonempty : {n | ∃ F, IsCover G F ∧ F.card = n}.Nonempty :=
  ⟨(edges G).card, edges G, isCover_edges G, rfl⟩

theorem isPacking_empty : IsPacking G ∅ :=
  ⟨Finset.empty_subset _, by intro t ht; simp at ht⟩

theorem packing_sizes_nonempty : {n | ∃ P, IsPacking G P ∧ P.card = n}.Nonempty :=
  ⟨0, ∅, isPacking_empty G, Finset.card_empty⟩

theorem packing_sizes_bddAbove : BddAbove {n | ∃ P, IsPacking G P ∧ P.card = n} :=
  ⟨(triangles G).card, by rintro n ⟨P, hP, rfl⟩; exact Finset.card_le_card hP.1⟩

/-- A maximum packing exists. -/
theorem exists_packing_card_eq_nu : ∃ P, IsPacking G P ∧ P.card = nu G :=
  Nat.sSup_mem (packing_sizes_nonempty G) (packing_sizes_bddAbove G)

/-- A minimum cover exists. -/
theorem exists_cover_card_eq_tau : ∃ F, IsCover G F ∧ F.card = tau G :=
  Nat.sInf_mem (cover_sizes_nonempty G)

theorem le_nu_of_isPacking {P : Finset (Finset V)} (hP : IsPacking G P) : P.card ≤ nu G :=
  le_csSup (packing_sizes_bddAbove G) ⟨P, hP, rfl⟩

theorem tau_le_of_isCover {F : Finset (Finset V)} (hF : IsCover G F) : tau G ≤ F.card :=
  Nat.sInf_le ⟨F, hF, rfl⟩

/-! ### The easy bound `ν ≤ τ` -/

/-- A packing is no larger than a cover: each packed triangle is hit by a cover
edge, and edge-disjointness makes those edges distinct. -/
theorem packing_card_le_cover_card {P F : Finset (Finset V)}
    (hP : IsPacking G P) (hF : IsCover G F) : P.card ≤ F.card := by
  classical
  -- choose, for each triangle, a covering edge it contains
  set g : Finset V → Finset V :=
    fun t => if h : ∃ e, e ∈ F ∧ e ∈ triEdges t then h.choose else ∅ with hg_def
  have hg : ∀ t ∈ P, g t ∈ F ∧ g t ∈ triEdges t := by
    intro t ht
    have hex : ∃ e, e ∈ F ∧ e ∈ triEdges t := hF.2 t (hP.1 ht)
    simp only [hg_def, dif_pos hex]
    exact hex.choose_spec
  refine Finset.card_le_card_of_injOn g (fun t ht => (hg t ht).1) ?_
  intro t₁ h₁ t₂ h₂ heq
  by_contra hne
  have hd := hP.2 t₁ h₁ t₂ h₂ hne
  have hm₁ : g t₁ ∈ triEdges t₁ := (hg t₁ h₁).2
  have hm₂ : g t₁ ∈ triEdges t₂ := by rw [heq]; exact (hg t₂ h₂).2
  exact (Finset.disjoint_left.mp hd hm₁) hm₂

/-- **The easy direction of Tuza:** `ν(G) ≤ τ(G)`. -/
theorem nu_le_tau : nu G ≤ tau G := by
  obtain ⟨F, hF, hFc⟩ := exists_cover_card_eq_tau G
  rw [← hFc]
  apply csSup_le (packing_sizes_nonempty G)
  rintro n ⟨P, hP, rfl⟩
  exact packing_card_le_cover_card G hP hF

end Tuza
