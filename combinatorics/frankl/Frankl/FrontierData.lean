import Mathlib.Tactic

/-!
# Finite Frontier Certificate Data

Reference: `combinatorics/frankl/research/entropy_transport_strategy.tex`

This file records the finite size-17 three-coordinate zero-shadow frontier
data in a Lean-friendly form.  The computational search in
`research/window_experiment.py --trace-three-frontier-shadow` found four
canonical count vectors remaining after propagation; each is paid by a
relaxed zero-fiber shadow certificate.

The data here is not yet the checker for the shadow search.  It is the stable
finite payload that such a checker should consume.
-/

set_option autoImplicit false

namespace Frankl

/-- A finite relaxed zero-shadow certificate for a three-coordinate frontier
count vector.  Trace masks are encoded as natural numbers `0..7`. -/
structure FrontierShadowRecord where
  counts : List Nat
  totalSize : Nat
  arrangementsChecked : Nat
  forcedZeroCoordMax : Nat
  zeroCoordCount : Nat
  zeroShadow : List Nat
  fiberShadows : List (Nat × List Nat)

/-- The `bit`-th membership test for a three-coordinate trace mask. -/
def traceBit (mask bit : Nat) : Bool :=
  decide (((mask / 2 ^ bit) % 2) = 1)

/-- The trace masks used by the frontier checker are exactly `0, ..., 7`. -/
def validTraceMask (mask : Nat) : Bool :=
  decide (mask < 8)

/-- Union of two three-coordinate trace masks. -/
def maskUnion (a b : Nat) : Nat :=
  (if traceBit a 0 || traceBit b 0 then 1 else 0) +
    (if traceBit a 1 || traceBit b 1 then 2 else 0) +
    (if traceBit a 2 || traceBit b 2 then 4 else 0)

/-- The arithmetic definition of `maskUnion` agrees with bitwise union on the
finite three-coordinate mask universe. -/
def maskUnionAgreesWithTraceBits : Bool :=
  (List.range 8).all fun a =>
    (List.range 8).all fun b =>
      (List.range 3).all fun bit =>
        decide (traceBit (maskUnion a b) bit = (traceBit a bit || traceBit b bit))

theorem maskUnion_agrees_with_traceBits :
    maskUnionAgreesWithTraceBits = true := by
  decide

/-- Boolean list membership for trace masks. -/
def containsMask (support : List Nat) (mask : Nat) : Bool :=
  decide (mask ∈ support)

/-- All masks in a finite support lie in the three-coordinate mask universe. -/
def allValidTraceMasks (support : List Nat) : Bool :=
  support.all validTraceMask

/-- A relaxed hidden-coordinate shadow support is closed under trace union. -/
def shadowSupportUnionClosed (support : List Nat) : Bool :=
  support.all fun a =>
    support.all fun b =>
      containsMask support (maskUnion a b)

/-- A fiber shadow is invariant under union with every zero-fiber shadow mask. -/
def zeroInvariantShadow (zeroShadow fiberShadow : List Nat) : Bool :=
  zeroShadow.all fun z =>
    fiberShadow.all fun f =>
      containsMask fiberShadow (maskUnion z f)

/-- Two source shadows join into the declared target shadow. -/
def shadowsJoinInto (left right out : List Nat) : Bool :=
  left.all fun a =>
    right.all fun b =>
      containsMask out (maskUnion a b)

/-- The shadow attached to a trace, using the zero-shadow for trace `0`. -/
def FrontierShadowRecord.lookupShadow (record : FrontierShadowRecord)
    (mask : Nat) : Option (List Nat) :=
  if mask = 0 then
    some record.zeroShadow
  else
    match record.fiberShadows.find? (fun entry => decide (entry.1 = mask)) with
    | some entry => some entry.2
    | none => none

/-- Every declared mask in the record is a valid three-coordinate trace mask. -/
def FrontierShadowRecord.masksValid (record : FrontierShadowRecord) : Bool :=
  allValidTraceMasks record.zeroShadow &&
    record.fiberShadows.all (fun entry =>
      validTraceMask entry.1 && allValidTraceMasks entry.2)

/-- The finite relaxed shadow constraints checked by the Python frontier
routine, specialized to the stored Lean payload. -/
def FrontierShadowRecord.shadowsValid (record : FrontierShadowRecord) : Bool :=
  shadowSupportUnionClosed record.zeroShadow &&
    record.fiberShadows.all (fun entry =>
      zeroInvariantShadow record.zeroShadow entry.2) &&
    record.fiberShadows.all (fun left =>
      record.fiberShadows.all (fun right =>
        match record.lookupShadow (maskUnion left.1 right.1) with
        | some out => shadowsJoinInto left.2 right.2 out
        | none => false))

/-- Complete finite validity predicate for one recorded frontier shadow
certificate.  It does not prove that the record came from an actual family;
it checks the relaxed shadow payload used to pay the finite frontier class. -/
def FrontierShadowRecord.valid (record : FrontierShadowRecord) : Bool :=
  decide (record.counts.length = 8) &&
    decide (record.counts.sum = record.totalSize) &&
    decide (record.totalSize ≤ 2 * record.forcedZeroCoordMax) &&
    record.masksValid &&
    record.shadowsValid

/-- The four size-17 frontier classes paid by zero-fiber shadow certificates. -/
def size17FrontierShadowRecords : List FrontierShadowRecord :=
  [
    {
      counts := [6, 0, 0, 3, 3, 0, 3, 2],
      totalSize := 17,
      arrangementsChecked := 114389,
      forcedZeroCoordMax := 12,
      zeroCoordCount := 3,
      zeroShadow := [0, 1, 2, 3, 5, 7],
      fiberShadows := [(3, [2, 3, 7]), (4, [5, 5, 7]), (6, [5, 6, 7]), (7, [6, 7])]
    },
    {
      counts := [8, 0, 1, 0, 1, 0, 1, 6],
      totalSize := 17,
      arrangementsChecked := 104,
      forcedZeroCoordMax := 11,
      zeroCoordCount := 3,
      zeroShadow := [0, 1, 2, 3, 4, 5, 6, 7],
      fiberShadows := [(2, [7]), (4, [7]), (6, [7]), (7, [1, 2, 3, 5, 6, 7])]
    },
    {
      counts := [8, 0, 1, 0, 1, 0, 2, 5],
      totalSize := 17,
      arrangementsChecked := 200,
      forcedZeroCoordMax := 11,
      zeroCoordCount := 3,
      zeroShadow := [0, 1, 2, 3, 4, 5, 6, 7],
      fiberShadows := [(2, [7]), (4, [7]), (6, [3, 7]), (7, [3, 4, 5, 6, 7])]
    },
    {
      counts := [8, 0, 1, 0, 2, 0, 1, 5],
      totalSize := 17,
      arrangementsChecked := 200,
      forcedZeroCoordMax := 11,
      zeroCoordCount := 3,
      zeroShadow := [0, 1, 2, 3, 4, 5, 6, 7],
      fiberShadows := [(2, [7]), (4, [3, 7]), (6, [7]), (7, [3, 4, 5, 6, 7])]
    }
  ]

theorem size17FrontierShadowRecords_length :
    size17FrontierShadowRecords.length = 4 := by
  rfl

/-- Every recorded size-17 shadow certificate forces a zero-coordinate
frequency at least half the total size. -/
theorem size17FrontierShadowRecords_paid :
    size17FrontierShadowRecords.all
      (fun record => decide (record.totalSize ≤ 2 * record.forcedZeroCoordMax)) =
        true := by
  decide

/-- Every recorded size-17 count vector has total size `17`. -/
theorem size17FrontierShadowRecords_countTotals :
    size17FrontierShadowRecords.all
      (fun record => decide (record.counts.sum = 17)) = true := by
  decide

/-- The recorded size-17 zero-shadow supports are closed under trace union. -/
theorem size17FrontierShadowRecords_zeroShadowsClosed :
    size17FrontierShadowRecords.all
      (fun record => shadowSupportUnionClosed record.zeroShadow) = true := by
  decide

/-- Lean checks the finite relaxed shadow predicates for every recorded
size-17 frontier certificate. -/
theorem size17FrontierShadowRecordsValid :
    size17FrontierShadowRecords.all FrontierShadowRecord.valid = true := by
  decide

end Frankl
