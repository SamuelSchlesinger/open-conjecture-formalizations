import Frankl.Certificates
import Mathlib.Tactic

/-!
# AHS Certificate Data

Reference: `combinatorics/frankl/research/ahs_hinge_certificate.json`

This file records the rational floors extracted from the current AHS hinge
certificate payload.  It proves the finite rational comparisons that Lean can
check immediately.  It does not yet prove that the transcendental interval
enclosures in the JSON are valid; that is the remaining analytic certificate
task.
-/

set_option autoImplicit false

namespace Frankl

def ahsRationalFloorDen : Nat :=
  100000000000000000000000000000000000000000000000000

def ahsI1RequiredFloor : ℚ :=
  3875 / 100000

def ahsI1MinRationalFloor : ℚ :=
  9248325641699922142378810983504789140653122789540 / ahsRationalFloorDen

def ahsI2MinGapRationalFloor : ℚ :=
  200067599000098888858296926772919412559450065424 / ahsRationalFloorDen

def ahsI3MarginRationalFloor : ℚ :=
  6672632523965810436636127842110740061105227242559 / ahsRationalFloorDen

theorem ahsI1MinRationalFloor_ge_required :
    ahsI1RequiredFloor ≤ ahsI1MinRationalFloor := by
  norm_num [ahsI1RequiredFloor, ahsI1MinRationalFloor, ahsRationalFloorDen]

theorem ahsI2MinGapRationalFloor_pos :
    0 < ahsI2MinGapRationalFloor := by
  norm_num [ahsI2MinGapRationalFloor, ahsRationalFloorDen]

theorem ahsI3MarginRationalFloor_pos :
    0 < ahsI3MarginRationalFloor := by
  norm_num [ahsI3MarginRationalFloor, ahsRationalFloorDen]

end Frankl
