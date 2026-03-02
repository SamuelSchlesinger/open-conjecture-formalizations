import Fortune.Basic
import Mathlib.Tactic.IntervalCases

namespace Fortune

theorem hasPrimeLeastFortunateOffset_one_to_four {n : Nat}
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    ∃ m : Nat, IsLeastFortunateOffset n m ∧ Nat.Prime m := by
  interval_cases n
  · exact hasPrimeLeastFortunateOffset_one
  · exact hasPrimeLeastFortunateOffset_two
  · exact hasPrimeLeastFortunateOffset_three
  · exact hasPrimeLeastFortunateOffset_four

end Fortune
