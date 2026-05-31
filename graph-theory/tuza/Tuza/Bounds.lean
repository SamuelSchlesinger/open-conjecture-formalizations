import Tuza.Basic

/-!
# Tuza's conjecture — the bound `τ ≤ 3ν`

This is the classical easy upper bound, and the known-territory companion to the
open `τ ≤ 2ν`.  Take a **maximum** edge-disjoint triangle packing `P`
(`|P| = ν`).  By maximality every triangle shares an edge with some triangle of
`P` (otherwise it could be added to `P`), so the `3ν` edges of `P` form a cover.
Hence `τ ≤ 3ν`.

Combined with `Basic.nu_le_tau`, this gives `ν(G) ≤ τ(G) ≤ 3·ν(G)`; Tuza's
conjecture sharpens the upper constant from `3` to `2`.
-/

set_option autoImplicit false

namespace Tuza

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Maximality.**  In a maximum packing `P`, every triangle of `G` shares an
edge with some triangle of `P` — otherwise it could be added, contradicting
maximality. -/
theorem exists_packing_mem_not_disjoint {P : Finset (Finset V)}
    (hP : IsPacking G P) (hmax : P.card = nu G) {t : Finset V} (ht : t ∈ triangles G) :
    ∃ t' ∈ P, ¬ Disjoint (triEdges t) (triEdges t') := by
  by_cases htP : t ∈ P
  · refine ⟨t, htP, ?_⟩
    rw [Finset.not_disjoint_iff]
    obtain ⟨e, he⟩ := triEdges_nonempty G ht
    exact ⟨e, he, he⟩
  · by_contra hcon
    push_neg at hcon
    have hP' : IsPacking G (insert t P) := by
      refine ⟨?_, ?_⟩
      · intro s hs
        rw [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · exact ht
        · exact hP.1 hs
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hcon b hb
        · exact (hcon a ha).symm
        · exact hP.2 a ha b hb hab
    have hcard : (insert t P).card = nu G + 1 := by
      rw [Finset.card_insert_of_notMem htP, hmax]
    have hle := le_nu_of_isPacking G hP'
    omega

/-- The edge set of a maximum packing is a triangle cover. -/
theorem isCover_packingEdges {P : Finset (Finset V)}
    (hP : IsPacking G P) (hmax : P.card = nu G) :
    IsCover G (P.biUnion triEdges) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨t, htP, het⟩ := he
    exact triEdges_subset_edges G (hP.1 htP) het
  · intro t ht
    obtain ⟨t', ht'P, hnd⟩ := exists_packing_mem_not_disjoint G hP hmax ht
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨e, het, het'⟩ := hnd
    exact ⟨e, Finset.mem_biUnion.mpr ⟨t', ht'P, het'⟩, het⟩

/-- A packing's edge set has at most `3·|P|` edges (three per triangle). -/
theorem packingEdges_card_le {P : Finset (Finset V)} (hP : IsPacking G P) :
    (P.biUnion triEdges).card ≤ 3 * P.card := by
  calc (P.biUnion triEdges).card
      ≤ ∑ t ∈ P, (triEdges t).card := Finset.card_biUnion_le
    _ = ∑ _t ∈ P, 3 := by
        apply Finset.sum_congr rfl
        intro t ht; exact triEdges_card G (hP.1 ht)
    _ = 3 * P.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **The bound `τ(G) ≤ 3·ν(G)`.**  A maximum packing's `3ν` edges cover every
triangle. -/
theorem tau_le_three_mul_nu : tau G ≤ 3 * nu G := by
  obtain ⟨P, hP, hmax⟩ := exists_packing_card_eq_nu G
  calc tau G ≤ (P.biUnion triEdges).card := tau_le_of_isCover G (isCover_packingEdges G hP hmax)
    _ ≤ 3 * P.card := packingEdges_card_le G hP
    _ = 3 * nu G := by rw [hmax]

/-- The full elementary sandwich `ν(G) ≤ τ(G) ≤ 3·ν(G)`. -/
theorem nu_le_tau_le_three_mul_nu : nu G ≤ tau G ∧ tau G ≤ 3 * nu G :=
  ⟨nu_le_tau G, tau_le_three_mul_nu G⟩

end Tuza
