import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Finite Entropy-Gain Certificates

Reference: `combinatorics/frankl/research/checklist.md`

The entropy-transport program separates raw coordinate entropy gain from the
total-correlation cost.  This file defines a small rational certificate format:
coordinate gain rows, a rational upper bound for total-correlation growth, and
a positive net margin.
-/

set_option autoImplicit false

namespace Frankl

/-- A rational lower bound for the entropy gain contributed by one coordinate. -/
structure CoordinateGainRow where
  coord : Nat
  gain : ℚ

/-- Sum of the rational coordinate-gain rows. -/
def totalCoordinateGain (rows : List CoordinateGainRow) : ℚ :=
  (rows.map CoordinateGainRow.gain).sum

/-- A finite rational certificate that raw coordinate gain beats the charged
total-correlation cost by a positive margin. -/
structure FiniteEntropyGainCertificate where
  coordinateGains : List CoordinateGainRow
  totalCorrelationBound : ℚ
  netMargin : ℚ

namespace FiniteEntropyGainCertificate

/-- Total certified coordinate gain. -/
def coordinateGain (cert : FiniteEntropyGainCertificate) : ℚ :=
  totalCoordinateGain cert.coordinateGains

/-- Boolean-free propositional validity of a finite entropy-gain certificate. -/
def Valid (cert : FiniteEntropyGainCertificate) : Prop :=
  0 < cert.netMargin ∧
    cert.totalCorrelationBound + cert.netMargin ≤ cert.coordinateGain

theorem totalCorrelationBound_lt_coordinateGain
    {cert : FiniteEntropyGainCertificate}
    (hcert : cert.Valid) :
    cert.totalCorrelationBound < cert.coordinateGain := by
  rcases hcert with ⟨hmargin, hle⟩
  linarith

/-- A one-row toy certificate, useful as a sanity check for the arithmetic
format before real JSON witnesses are translated into Lean data. -/
def toyPositive : FiniteEntropyGainCertificate :=
  {
    coordinateGains := [{ coord := 0, gain := 3 / 10 }],
    totalCorrelationBound := 1 / 10,
    netMargin := 1 / 10
  }

theorem toyPositive_valid : toyPositive.Valid := by
  constructor <;> norm_num [toyPositive, coordinateGain, totalCoordinateGain, Valid]

theorem toyPositive_beats_cost :
    toyPositive.totalCorrelationBound < toyPositive.coordinateGain :=
  totalCorrelationBound_lt_coordinateGain toyPositive_valid

end FiniteEntropyGainCertificate

end Frankl
