import Singmaster.Basic

/-!
# Singmaster's conjecture — small cases (computational sanity)

The Singmaster multiplicity `singmasterCount a` is a `Finset` cardinality over a
finite box, hence the kernel can evaluate it for small `a` (`decide`, no
`native_decide`).  These checks pin down the counting infrastructure:

* `2` appears once (`C(2,1)`);
* `6` appears three times (`C(6,1) = C(6,5) = C(4,2)`);
* `10` appears four times (`C(10,1) = C(10,9) = C(5,2) = C(5,3)`).

Larger record multiplicities are documented in `research/exploration.md` (they
are out of reach for `decide`, since `Nat.choose` recurses without memoization):
`120` and `210` appear `6` times, and `3003 = C(3003,1) = C(78,2) = C(15,5) =
C(14,6)` (with symmetric partners) appears **8** times — the largest known, the
basis for Singmaster's conjectured constant `C = 8`.
-/

set_option autoImplicit false

namespace Singmaster

/-- `2` appears exactly once in Pascal's triangle (only `C(2,1)`). -/
theorem singmasterCount_two : singmasterCount 2 = 1 := by decide

/-- `6 = C(6,1) = C(6,5) = C(4,2)` appears three times. -/
theorem singmasterCount_six : singmasterCount 6 = 3 := by decide

/-- `10 = C(10,1) = C(10,9) = C(5,2) = C(5,3)` appears four times — so any
Singmaster constant must be at least `4`. -/
theorem singmasterCount_ten : singmasterCount 10 = 4 := by decide

end Singmaster
