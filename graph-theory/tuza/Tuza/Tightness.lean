import Tuza.Bounds

/-!
# Tuza's conjecture — tightness of the factor `2`

The complete graph `K₄` (on `Fin 4`) has `ν(K₄) = 1` and `τ(K₄) = 2`, so
`τ = 2·ν`.  This shows the constant `2` in the conjecture **cannot be improved**.

* `ν(K₄) = 1`: any two distinct triangles of `K₄` share an edge (they meet in two
  of the four vertices), so no two are edge-disjoint — a packing has at most one
  triangle.
* `τ(K₄) = 2`: the two independent edges `{0,1}, {2,3}` hit all four triangles
  (so `τ ≤ 2`); and no single edge lies in all four triangles (each edge misses
  two of them), so `τ ≥ 2`.

The three `K₄`-specific combinatorial facts are discharged by the kernel
(`decide`); the optimization bounds are then assembled from the general
`ν`/`τ` API.
-/

set_option autoImplicit false

namespace Tuza

/-- `K₄`, the complete graph on four vertices. -/
abbrev G4 : SimpleGraph (Fin 4) := ⊤

/-- Distinct triangles of `K₄` share an edge. -/
theorem k4_share_edge : ∀ t₁ ∈ triangles G4, ∀ t₂ ∈ triangles G4, t₁ ≠ t₂ →
    ¬ Disjoint (triEdges t₁) (triEdges t₂) := by decide

/-- Every edge of `K₄` misses some triangle. -/
theorem k4_edge_misses : ∀ e ∈ edges G4, ∃ t ∈ triangles G4, e ∉ triEdges t := by decide

/-- The two independent edges `{0,1}, {2,3}` meet every triangle of `K₄`. -/
theorem k4_cover : ∀ t ∈ triangles G4,
    ∃ e ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))), e ∈ triEdges t := by decide

/-! ### `ν(K₄) = 1` -/

theorem nu_K4_le_one : nu G4 ≤ 1 := by
  apply csSup_le (packing_sizes_nonempty G4)
  rintro n ⟨P, hP, rfl⟩
  by_contra h
  push_neg at h
  obtain ⟨t₁, h₁, t₂, h₂, hne⟩ := Finset.one_lt_card.mp h
  exact k4_share_edge t₁ (hP.1 h₁) t₂ (hP.1 h₂) hne (hP.2 t₁ h₁ t₂ h₂ hne)

theorem one_le_nu_K4 : 1 ≤ nu G4 := by
  have hP : IsPacking G4 {{0, 1, 2}} := by
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [Finset.mem_singleton] at ht; subst ht; decide
    · intro a ha b hb hab
      rw [Finset.mem_singleton] at ha hb; subst ha; subst hb; exact absurd rfl hab
  have h := le_nu_of_isPacking G4 hP
  rwa [Finset.card_singleton] at h

theorem nu_K4 : nu G4 = 1 := le_antisymm nu_K4_le_one one_le_nu_K4

/-! ### `τ(K₄) = 2` -/

theorem tau_K4_le_two : tau G4 ≤ 2 := by
  have hcover : IsCover G4 {{0, 1}, {2, 3}} := by
    refine ⟨?_, k4_cover⟩
    intro e he
    rw [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> decide
  have h := tau_le_of_isCover G4 hcover
  have hc : ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))).card = 2 := by decide
  omega

theorem two_le_cover_card {F : Finset (Finset (Fin 4))} (hF : IsCover G4 F) : 2 ≤ F.card := by
  by_contra h
  push_neg at h
  have hcase : F.card = 0 ∨ F.card = 1 := by omega
  rcases hcase with hc | hc
  · rw [Finset.card_eq_zero] at hc; subst hc
    obtain ⟨e, he, _⟩ := hF.2 {0, 1, 2} (by decide)
    exact Finset.notMem_empty e he
  · rw [Finset.card_eq_one] at hc
    obtain ⟨e, hFe⟩ := hc
    have heE : e ∈ edges G4 := hF.1 (by rw [hFe]; exact Finset.mem_singleton_self e)
    obtain ⟨t, ht, hte⟩ := k4_edge_misses e heE
    obtain ⟨e', he', he'2⟩ := hF.2 t ht
    rw [hFe, Finset.mem_singleton] at he'; subst he'
    exact hte he'2

theorem two_le_tau_K4 : 2 ≤ tau G4 :=
  le_csInf (cover_sizes_nonempty G4) (by rintro n ⟨F, hF, rfl⟩; exact two_le_cover_card hF)

theorem tau_K4 : tau G4 = 2 := le_antisymm tau_K4_le_two two_le_tau_K4

/-! ### Tightness -/

/-- **The factor `2` in Tuza's conjecture is best possible:** `K₄` realizes
`τ = 2·ν` (with `ν = 1`, so the example is non-trivial). -/
theorem tuza_tight : tau G4 = 2 * nu G4 ∧ 1 ≤ nu G4 := by
  rw [tau_K4, nu_K4]; exact ⟨rfl, le_refl 1⟩

end Tuza
