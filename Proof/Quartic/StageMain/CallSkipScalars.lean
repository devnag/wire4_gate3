import Proof.Quartic.StageMain.CallSkipSpec

/-!
# The integer, Boolean and rational fields of a call

The original circuit and radius encodings used by `prop:time`,
paper/paper.tex, have self-delimiting sign, magnitude
and denominator fields. These scanners consume the literal encoding,
including zero magnitudes and either sign tag, and count every bit.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

def skipInt : St VV MM := .seq scanNat scanNat

theorem skipInt_spec : ScanSpec skipInt intWord atomScratch (fun L => 133 * (L + 1)) := by
  have h := (scanNat_spec.map (fun z : ℤ => if z < 0 then 1 else 0)).seq
    (scanNat_spec.map Int.natAbs)
  exact h.weaken (by intro x hx; simp only [List.mem_append] at hx; tauto)
    (by intro L; omega)

theorem skipBit_spec : ScanSpec scanNat bitWord atomScratch (fun L => 66 * (L + 1)) :=
  scanNat_spec.map (fun b : Bool => if b then 1 else 0)

def skipRat : St VV MM := .seq skipInt scanNat

theorem skipRat_spec : ScanSpec skipRat ratWord atomScratch (fun L => 200 * (L + 1)) := by
  have h := (skipInt_spec.map Rat.num).seq (scanNat_spec.map Rat.den)
  exact h.weaken (by intro x hx; simp only [List.mem_append] at hx; tauto)
    (by intro L; omega)

theorem natWord_positive (x : ℕ) : 0 < (natWord x).length := by rw [natWord_length]; omega

theorem intWord_positive (x : ℤ) : 0 < (intWord x).length := by
  simp only [intWord, List.length_append, natWord_length]
  omega

theorem bitWord_positive (x : Bool) : 0 < (bitWord x).length := natWord_positive _

end NearQuarticWires.StageMain.CallSkip
