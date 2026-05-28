import Frankl.Basic
import Mathlib.Tactic

/-!
# Trace Fibers

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

Trace fibers split a union-closed family according to its visible coordinates.
This file formalizes the basic set-theoretic layer: traces, fibers over a
trace, and the induced join operation on the trace support.
-/

set_option autoImplicit false

namespace Frankl

variable {α : Type*} [DecidableEq α]

/-- The trace of a member-set `A` on a visible coordinate set `S`. -/
def traceOn (S A : Finset α) : Finset α :=
  A ∩ S

/-- The fiber of family members whose trace on `S` is `T`. -/
def traceFiber (S : Finset α) (F : Finset (Finset α)) (T : Finset α) :
    Finset (Finset α) :=
  F.filter fun A => traceOn S A = T

/-- The set of all traces realized by members of `F`. -/
def traceSupport (S : Finset α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F.image (traceOn S)

theorem mem_traceFiber {S T : Finset α} {F : Finset (Finset α)}
    {A : Finset α} :
    A ∈ traceFiber S F T ↔ A ∈ F ∧ traceOn S A = T := by
  simp [traceFiber]

theorem mem_traceSupport {S T : Finset α} {F : Finset (Finset α)} :
    T ∈ traceSupport S F ↔ ∃ A ∈ F, traceOn S A = T := by
  simp [traceSupport]

theorem traceOn_union (S A B : Finset α) :
    traceOn S (A ∪ B) = traceOn S A ∪ traceOn S B := by
  ext x
  simp [traceOn]
  constructor
  · intro h
    rcases h with ⟨hxA | hxB, hxS⟩
    · exact Or.inl ⟨hxA, hxS⟩
    · exact Or.inr ⟨hxB, hxS⟩
  · intro h
    rcases h with ⟨hxA, hxS⟩ | ⟨hxB, hxS⟩
    · exact ⟨Or.inl hxA, hxS⟩
    · exact ⟨Or.inr hxB, hxS⟩

theorem union_mem_traceFiber_of_mem {S T U : Finset α}
    {F : Finset (Finset α)} {A B : Finset α}
    (hF : IsUnionClosed F)
    (hA : A ∈ traceFiber S F T)
    (hB : B ∈ traceFiber S F U) :
    A ∪ B ∈ traceFiber S F (T ∪ U) := by
  rw [mem_traceFiber] at hA hB ⊢
  refine ⟨hF A hA.1 B hB.1, ?_⟩
  rw [traceOn_union, hA.2, hB.2]

/-- The trace support of a union-closed family is union-closed. -/
theorem isUnionClosed_traceSupport {S : Finset α} {F : Finset (Finset α)}
    (hF : IsUnionClosed F) :
    IsUnionClosed (traceSupport S F) := by
  intro T hT U hU
  rw [mem_traceSupport] at hT hU ⊢
  rcases hT with ⟨A, hA, rfl⟩
  rcases hU with ⟨B, hB, rfl⟩
  refine ⟨A ∪ B, hF A hA B hB, ?_⟩
  rw [traceOn_union]

/-- Trace-fiber Horn propagation: if every member of the output trace fiber
contains `x`, then the union of an input from the `T` fiber and an input from
the `U` fiber forces `x` to appear on at least one side. -/
theorem mem_left_or_mem_right_of_traceFiber_union_all {S T U : Finset α}
    {F : Finset (Finset α)} {A B : Finset α} {x : α}
    (hF : IsUnionClosed F)
    (hAll : ∀ C ∈ traceFiber S F (T ∪ U), x ∈ C)
    (hA : A ∈ traceFiber S F T)
    (hB : B ∈ traceFiber S F U) :
    x ∈ A ∨ x ∈ B := by
  have hUnion : A ∪ B ∈ traceFiber S F (T ∪ U) :=
    union_mem_traceFiber_of_mem hF hA hB
  have hxUnion : x ∈ A ∪ B := hAll (A ∪ B) hUnion
  simpa using hxUnion

theorem mem_right_of_traceFiber_union_all_of_not_mem_left {S T U : Finset α}
    {F : Finset (Finset α)} {A B : Finset α} {x : α}
    (hF : IsUnionClosed F)
    (hAll : ∀ C ∈ traceFiber S F (T ∪ U), x ∈ C)
    (hA : A ∈ traceFiber S F T)
    (hB : B ∈ traceFiber S F U)
    (hxA : x ∉ A) :
    x ∈ B := by
  rcases mem_left_or_mem_right_of_traceFiber_union_all hF hAll hA hB with
    hxA' | hxB
  · exact False.elim (hxA hxA')
  · exact hxB

theorem mem_left_of_traceFiber_union_all_of_not_mem_right {S T U : Finset α}
    {F : Finset (Finset α)} {A B : Finset α} {x : α}
    (hF : IsUnionClosed F)
    (hAll : ∀ C ∈ traceFiber S F (T ∪ U), x ∈ C)
    (hA : A ∈ traceFiber S F T)
    (hB : B ∈ traceFiber S F U)
    (hxB : x ∉ B) :
    x ∈ A := by
  rcases mem_left_or_mem_right_of_traceFiber_union_all hF hAll hA hB with
    hxA | hxB'
  · exact hxA
  · exact False.elim (hxB hxB')

end Frankl
