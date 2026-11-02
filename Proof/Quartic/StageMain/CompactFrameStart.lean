import Proof.Quartic.StageMain.CompactFrameLoop

/-!
# The leading marker of the retained witness frame

The witness of `sec:algorithm`, paper/paper.tex,
and Step 4: even an empty witness contributes its
terminal marker to the literal retained preparation word.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift CallSkip

def copyFrameStart : St VV MM := .seq (.op (.rdI t0))
  (.seq (.op (.wrM compactStore t0)) (.op (.inc lengthCounter)))

def frameStart (a : DS VV MM) (marker : Bool) : DS VV MM :=
  { (a.set t0 marker.toNat).set lengthCounter (a.env lengthCounter + 1) with
    ip := a.ip + 1
    ram := Function.update a.ram compactStore (a.ram compactStore ++ [marker.toNat])
    rc := Function.update a.rc compactStore (a.rc compactStore + 1) }

theorem frameStart_fr (a : DS VV MM) (marker : Bool) :
    Fr a (frameStart a marker) frameScratch := by
  intro y hy
  simp only [frameScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [frameStart, DS.set, Function.update_of_ne hy.1, Function.update_of_ne hy.2.2]

theorem copyFrameStart_run (C : Ctx) (a : DS VV MM) (marker : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip = marker :: rest)
    (hcursor : a.rc compactStore = (a.ram compactStore).length)
    (hcap : a.env lengthCounter + 1 < 2 ^ C.Wd) :
    Hs C copyFrameStart a 5 (fun b => b = frameStart a marker) := by
  unfold copyFrameStart
  refine Hs.seq (t2 := 3) (readInputBit_spec C t0 a marker rest hin) ?_
  rintro b rfl
  refine Hs.seq (t2 := 1) (hs_wrM C compactStore t0 _ hcursor.le) ?_
  rintro b rfl
  refine (hs_inc C lengthCounter _ ?_).mono le_rfl ?_
  · simpa (config := {decide := true}) [DS.put, DS.set] using hcap
  rintro b rfl
  simp (config := {decide := true}) [frameStart, DS.put, DS.set, putAt, hcursor]

end NearQuarticWires.StageMain.Compact
