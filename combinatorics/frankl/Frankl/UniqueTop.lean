import Mathlib.Tactic

/-!
# Unique-Top Symbolic Propagation

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file records the case-split arithmetic core of the unique-top symbolic
propagation proposition.  The trace-fiber lemmas supply the two cases:

* if the `B` fiber is entirely hit, the occurrence count is at least
  `r + b + 3`;
* otherwise the singleton top fiber forces the `C` and `D` fibers entirely,
  giving at least `r + c + d + 2`.

The theorem below packages the final symbolic bound used by the parametric
three-coordinate obstruction.
-/

set_option autoImplicit false

namespace Frankl

/-- Arithmetic core of the unique-top symbolic propagation proposition. -/
theorem uniqueTop_symbolicPropagation_bound {r b c d hits : Nat}
    {allB : Prop} [Decidable allB]
    (hAllB : allB → r + b + 3 ≤ hits)
    (hNotAllB : ¬ allB → r + c + d + 2 ≤ hits) :
    r + min (b + 3) (c + d + 2) ≤ hits := by
  by_cases hB : allB
  · have h : r + b + 3 ≤ hits := hAllB hB
    have hmin : r + min (b + 3) (c + d + 2) ≤ r + b + 3 := by
      omega
    exact le_trans hmin h
  · have h : r + c + d + 2 ≤ hits := hNotAllB hB
    have hmin : r + min (b + 3) (c + d + 2) ≤ r + c + d + 2 := by
      omega
    exact le_trans hmin h

variable {α : Type*} [DecidableEq α]

/-- Five trace fibers in the unique-top obstruction pattern.  The names follow
the LaTeX note: `A` is the zero fiber, `T` is the singleton top fiber, and
`B`, `C`, `D` are the three nonzero intermediate fibers. -/
structure TraceProfile5 (α : Type*) [DecidableEq α] where
  A : Finset (Finset α)
  B : Finset (Finset α)
  C : Finset (Finset α)
  D : Finset (Finset α)
  T : Finset (Finset α)
  joinBC : ∀ b ∈ B, ∀ c ∈ C, b ∪ c ∈ T
  joinBD : ∀ b ∈ B, ∀ d ∈ D, b ∪ d ∈ T
  joinCD : ∀ c ∈ C, ∀ d ∈ D, c ∪ d ∈ D

namespace TraceProfile5

/-- The singleton-top hypothesis used by the symbolic propagation argument. -/
def SingletonTop (profile : TraceProfile5 α) : Prop :=
  profile.T.card = 1

/-- Number of members of one fiber containing a hidden coordinate. -/
def fiberHitCount (h : α) (fiber : Finset (Finset α)) : Nat :=
  (fiber.filter fun S => h ∈ S).card

/-- Number of zero-fiber members hit by a hidden coordinate. -/
def zeroHits (profile : TraceProfile5 α) (h : α) : Nat :=
  fiberHitCount h profile.A

/-- Total hits across the five fibers of the profile. -/
def totalHits (profile : TraceProfile5 α) (h : α) : Nat :=
  fiberHitCount h profile.A +
    fiberHitCount h profile.B +
    fiberHitCount h profile.C +
    fiberHitCount h profile.D +
    fiberHitCount h profile.T

theorem fiberHitCount_eq_card_of_forall_mem {h : α}
    {fiber : Finset (Finset α)}
    (hall : ∀ S ∈ fiber, h ∈ S) :
    fiberHitCount h fiber = fiber.card := by
  have hfilter : fiber.filter (fun S => h ∈ S) = fiber := by
    ext S
    by_cases hS : S ∈ fiber
    · simp [hS, hall S hS]
    · simp [hS]
  simp [fiberHitCount, hfilter]

theorem one_le_fiberHitCount_of_mem {h : α} {fiber : Finset (Finset α)}
    {S : Finset α} (hS : S ∈ fiber) (hh : h ∈ S) :
    1 ≤ fiberHitCount h fiber := by
  have hmem : S ∈ fiber.filter (fun U => h ∈ U) := by
    simp [hS, hh]
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨S, hmem⟩)

theorem eq_top_of_mem_singletonTop {profile : TraceProfile5 α}
    {top S : Finset α}
    (hcard : profile.SingletonTop)
    (htop : top ∈ profile.T)
    (hS : S ∈ profile.T) :
    S = top := by
  rcases Finset.card_eq_one.mp hcard with ⟨only, hT⟩
  rw [hT] at htop hS
  have htopOnly : top = only := by
    simpa using htop
  have hSOnly : S = only := by
    simpa using hS
  exact hSOnly.trans htopOnly.symm

/-- If every member of `B` contains `h`, and one member of each of `C`, `D`,
and `T` contains `h`, then the all-`B` branch gives `r + b + 3` hits. -/
theorem allB_hits_lower_bound (profile : TraceProfile5 α) {h : α}
    (hB : ∀ b ∈ profile.B, h ∈ b)
    (hC : ∃ c ∈ profile.C, h ∈ c)
    (hD : ∃ d ∈ profile.D, h ∈ d)
    (hT : ∃ t ∈ profile.T, h ∈ t) :
    profile.zeroHits h + profile.B.card + 3 ≤ profile.totalHits h := by
  rcases hC with ⟨c, hc, hhc⟩
  rcases hD with ⟨d, hd, hhd⟩
  rcases hT with ⟨t, ht, hht⟩
  have hBcount : fiberHitCount h profile.B = profile.B.card :=
    fiberHitCount_eq_card_of_forall_mem hB
  have hCpos : 1 ≤ fiberHitCount h profile.C :=
    one_le_fiberHitCount_of_mem hc hhc
  have hDpos : 1 ≤ fiberHitCount h profile.D :=
    one_le_fiberHitCount_of_mem hd hhd
  have hTpos : 1 ≤ fiberHitCount h profile.T :=
    one_le_fiberHitCount_of_mem ht hht
  unfold zeroHits totalHits
  rw [hBcount]
  omega

/-- In the not-all-`B` branch, one `B` member omitting `h` forces all members
of `C` and `D` to contain `h`, provided their joins land in the singleton top
fiber whose unique member contains `h`. -/
theorem notAllB_hits_lower_bound (profile : TraceProfile5 α) {h : α}
    {top b₀ : Finset α}
    (hcard : profile.SingletonTop)
    (htop : top ∈ profile.T)
    (hhtop : h ∈ top)
    (hb₀ : b₀ ∈ profile.B)
    (hnb₀ : h ∉ b₀)
    (hBhit : ∃ b ∈ profile.B, h ∈ b) :
    profile.zeroHits h + profile.C.card + profile.D.card + 2 ≤
      profile.totalHits h := by
  have hAllC : ∀ c ∈ profile.C, h ∈ c := by
    intro c hc
    have hjoin : b₀ ∪ c = top :=
      eq_top_of_mem_singletonTop hcard htop (profile.joinBC b₀ hb₀ c hc)
    have hUnion : h ∈ b₀ ∪ c := by
      simpa [hjoin] using hhtop
    rcases (by simpa using hUnion : h ∈ b₀ ∨ h ∈ c) with hb | hcHit
    · exact False.elim (hnb₀ hb)
    · exact hcHit
  have hAllD : ∀ d ∈ profile.D, h ∈ d := by
    intro d hd
    have hjoin : b₀ ∪ d = top :=
      eq_top_of_mem_singletonTop hcard htop (profile.joinBD b₀ hb₀ d hd)
    have hUnion : h ∈ b₀ ∪ d := by
      simpa [hjoin] using hhtop
    rcases (by simpa using hUnion : h ∈ b₀ ∨ h ∈ d) with hb | hdHit
    · exact False.elim (hnb₀ hb)
    · exact hdHit
  rcases hBhit with ⟨b, hb, hhb⟩
  have hBpos : 1 ≤ fiberHitCount h profile.B :=
    one_le_fiberHitCount_of_mem hb hhb
  have hTpos : 1 ≤ fiberHitCount h profile.T :=
    one_le_fiberHitCount_of_mem htop hhtop
  have hCcount : fiberHitCount h profile.C = profile.C.card :=
    fiberHitCount_eq_card_of_forall_mem hAllC
  have hDcount : fiberHitCount h profile.D = profile.D.card :=
    fiberHitCount_eq_card_of_forall_mem hAllD
  unfold zeroHits totalHits
  rw [hCcount, hDcount]
  omega

/-- The two propagation branches feed the arithmetic core. -/
theorem symbolicPropagation_from_cases (profile : TraceProfile5 α) {h : α}
    (hAllB :
      (∀ b ∈ profile.B, h ∈ b) →
        profile.zeroHits h + profile.B.card + 3 ≤ profile.totalHits h)
    (hNotAllB :
      ¬ (∀ b ∈ profile.B, h ∈ b) →
        profile.zeroHits h + profile.C.card + profile.D.card + 2 ≤
          profile.totalHits h) :
    profile.zeroHits h +
        min (profile.B.card + 3) (profile.C.card + profile.D.card + 2) ≤
      profile.totalHits h := by
  exact uniqueTop_symbolicPropagation_bound
    (r := profile.zeroHits h)
    (b := profile.B.card)
    (c := profile.C.card)
    (d := profile.D.card)
    (hits := profile.totalHits h)
    (allB := ∀ b ∈ profile.B, h ∈ b)
    hAllB
    hNotAllB

/-- A convenient packed unique-top propagation theorem.  The bottom-fiber
propagation inputs are represented by the existence of already-hit members in
`B`, `C`, `D`, and by the unique top member containing `h`. -/
theorem uniqueTop_hits_lower_bound (profile : TraceProfile5 α) {h : α}
    {top : Finset α}
    (hcard : profile.SingletonTop)
    (htop : top ∈ profile.T)
    (hhtop : h ∈ top)
    (hBhit : ∃ b ∈ profile.B, h ∈ b)
    (hChit : ∃ c ∈ profile.C, h ∈ c)
    (hDhit : ∃ d ∈ profile.D, h ∈ d) :
    profile.zeroHits h +
        min (profile.B.card + 3) (profile.C.card + profile.D.card + 2) ≤
      profile.totalHits h := by
  classical
  refine symbolicPropagation_from_cases profile ?_ ?_
  · intro hAllB
    exact profile.allB_hits_lower_bound hAllB hChit hDhit ⟨top, htop, hhtop⟩
  · intro hNotAllB
    have hb₀ : ∃ b₀ ∈ profile.B, h ∉ b₀ := by
      by_contra hnone
      apply hNotAllB
      intro b hb
      by_contra hnb
      exact hnone ⟨b, hb, hnb⟩
    rcases hb₀ with ⟨b₀, hb₀, hnb₀⟩
    exact profile.notAllB_hits_lower_bound hcard htop hhtop hb₀ hnb₀ hBhit

end TraceProfile5

/-- Instantiation of the arithmetic core on the parametric obstruction
`r = 2`, `b = k`, `c = k`, `d = 2`. -/
theorem uniqueTop_parametric_obstruction_occurrences {k hits : Nat}
    (_hk : 2 ≤ k)
    (hpropagation : 2 + min (k + 3) (k + 2 + 2) ≤ hits) :
    k + 5 ≤ hits := by
  omega

/-- The parametric obstruction occurrence count is already a Frankl half-bound
for a family of size `2k + 7`. -/
theorem uniqueTop_parametric_obstruction_half {k hits : Nat}
    (_hk : 2 ≤ k)
    (hhits : k + 5 ≤ hits) :
    2 * k + 7 ≤ 2 * hits := by
  omega

end Frankl
