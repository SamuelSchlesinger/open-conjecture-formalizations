import Frankl.Basic

set_option autoImplicit false

namespace Frankl

variable {α : Type*} [DecidableEq α]

theorem franklConjectureFor_empty :
    FranklConjectureFor (∅ : Finset (Finset α)) := by
  intro _hF hNonempty
  rcases hNonempty with ⟨A, hA, _hAne⟩
  simp at hA

theorem franklConjectureFor_singleton (S : Finset α) :
    FranklConjectureFor ({S} : Finset (Finset α)) := by
  intro _hF hNonempty
  rcases hNonempty with ⟨A, hA, hAne⟩
  have hAS : A = S := by
    simpa using hA
  subst A
  rcases hAne with ⟨x, hxS⟩
  refine ⟨x, ?_, ?_⟩
  · rw [mem_familyUnion]
    exact ⟨S, by simp, hxS⟩
  · have hfilter : memberSubfamily x ({S} : Finset (Finset α)) = {S} := by
      ext T
      constructor
      · intro hT
        rw [mem_memberSubfamily] at hT
        simpa using hT.1
      · intro hT
        have hTS : T = S := by
          simpa using hT
        subst T
        rw [mem_memberSubfamily]
        exact ⟨by simp, hxS⟩
    have hcount : memberCount x ({S} : Finset (Finset α)) = 1 := by
      simp [memberCount, hfilter]
    simp [hcount]

theorem franklConjectureFor_singleton_set (x : α) :
    FranklConjectureFor ({({x} : Finset α)} : Finset (Finset α)) := by
  exact franklConjectureFor_of_singleton_mem (F := {({x} : Finset α)}) (x := x) (by simp)

end Frankl
