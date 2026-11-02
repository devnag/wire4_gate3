import Proof.Quartic.StageLift.FrameRead
import Proof.Quartic.StageMain.SampleDigits

/-!
# Reading the chosen seed from the main-pass source

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: the framed chosen seed is accumulated
in low-bit-first order before the repeated sample evaluations.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

def seedPower : Fin VV := 79

def seedReadScratch : List (Fin VV) := [t0, t1, t3, seed, seedPower]

def seedReadBody : St VV MM :=
  .seq (.op (.rdI t1)) (.seq (.op (.mul t1 seedPower t3))
    (.seq (.op (.add seed t3)) (.seq (.op (.shl seedPower)) (.op (.rdI t0)))))

def seedReadStep (a : DS VV MM) (bit marker : Bool) : DS VV MM :=
  { (((a.set t1 bit.toNat).set t3 (bit.toNat * a.env seedPower)).set seed
      (a.env seed + bit.toNat * a.env seedPower)).set seedPower (2 * a.env seedPower) with
    env := Function.update
      ((((a.set t1 bit.toNat).set t3 (bit.toNat * a.env seedPower)).set seed
        (a.env seed + bit.toNat * a.env seedPower)).set seedPower (2 * a.env seedPower)).env
      t0 marker.toNat
    ip := a.ip + 2 }

theorem seedReadStep_fr (a : DS VV MM) (bit marker : Bool) :
    Fr a (seedReadStep a bit marker) seedReadScratch := by
  intro y hy
  simp only [seedReadScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [seedReadStep, DS.set, Function.update_of_ne hy.1,
    Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.1,
    Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.2.2]

theorem seedReadBody_run (C : Ctx) (a : DS VV MM) (bit marker : Bool)
    (rest : List Bool) (hin : C.inp.drop a.ip = bit :: marker :: rest)
    (hvalue : a.env seed + bit.toNat * a.env seedPower < 2 ^ C.Wd)
    (hpower : 2 * a.env seedPower < 2 ^ C.Wd) :
    Hs C seedReadBody a 9 (fun b => b = seedReadStep a bit marker) := by
  unfold seedReadBody
  refine Hs.seq (t2 := 7) (readInputBit_spec C t1 a bit (marker :: rest) hin) ?_
  rintro b rfl
  refine Hs.seq (t2 := 5) (hs_mul C t1 seedPower t3 _ (by decide) (by decide) (by decide) ?_) ?_
  · simp (config := {decide := true}) [DS.set]
    omega
  rintro b rfl
  refine Hs.seq (t2 := 3) (hs_add C seed t3 _ (by decide) ?_) ?_
  · simpa (config := {decide := true}) [DS.set] using hvalue
  rintro b rfl
  refine Hs.seq (t2 := 1) (hs_shl C seedPower _ ?_) ?_
  · simpa (config := {decide := true}) [DS.set] using hpower
  rintro b rfl
  have hnext : C.inp.drop (a.ip + 1) = marker :: rest := by
    rw [← List.drop_drop, hin]
    rfl
  refine (readInputBit_spec C t0 _ marker rest hnext).mono le_rfl ?_
  rintro b rfl
  simp (config := {decide := true}) [seedReadStep, DS.set]

end NearQuarticWires.StageMain.SampleCells
