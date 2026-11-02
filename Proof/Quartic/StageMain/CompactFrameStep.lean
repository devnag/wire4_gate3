import Proof.Quartic.StageMain.CompactCopy

/-!
# Retaining both markers and witness payload bits

The witness of `sec:algorithm`, paper/paper.tex,
is part of the finite input reused by Step 4. Each
payload bit and its following frame marker are copied physically,
while the runtime compact-prefix length grows by two.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift
open CallSkip

def frameScratch : List (Fin VV) := [t0, t1, lengthCounter]

def copyFrameBody : St VV MM :=
  .seq (.op (.rdI t1)) (.seq (.op (.wrM compactStore t1))
    (.seq (.op (.rdI t0)) (.seq (.op (.wrM compactStore t0)) (.op (.add lengthCounter v2)))))

def frameStep (a : DS VV MM) (bit marker : Bool) : DS VV MM :=
  { ((a.set t1 bit.toNat).set t0 marker.toNat).set lengthCounter
      (a.env lengthCounter + 2) with
    ip := a.ip + 2
    ram := Function.update a.ram compactStore (a.ram compactStore ++ [bit.toNat, marker.toNat])
    rc := Function.update a.rc compactStore (a.rc compactStore + 2) }

theorem frameStep_fr (a : DS VV MM) (bit marker : Bool) :
    Fr a (frameStep a bit marker) frameScratch := by
  intro y hy
  simp only [frameScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [frameStep, DS.set, Function.update_of_ne hy.1,
    Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2]

theorem copyFrameBody_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (bit marker : Bool)
    (rest : List Bool) (hin : C.inp.drop a.ip = bit :: marker :: rest)
    (hcursor : a.rc compactStore = (a.ram compactStore).length)
    (hcap : a.env lengthCounter + 2 < 2 ^ C.Wd) :
    Hs C copyFrameBody a 9 (fun b => b = frameStep a bit marker) := by
  unfold copyFrameBody
  refine Hs.seq (t2 := 7) (readInputBit_spec C t1 a bit (marker :: rest) hin) ?_
  rintro b rfl
  refine Hs.seq (t2 := 5) (hs_wrM C compactStore t1 _ hcursor.le) ?_
  rintro b rfl
  have hnext : C.inp.drop (a.ip + 1) = marker :: rest := by
    rw [← List.drop_drop, hin]
    rfl
  refine Hs.seq (t2 := 3) (readInputBit_spec C t0 _ marker rest hnext) ?_
  rintro b rfl
  refine Hs.seq (t2 := 1) (hs_wrM C compactStore t0 _ ?_) ?_
  · simp only [DS.put]
    change a.rc compactStore + 1 ≤ (putAt (a.ram compactStore) (a.rc compactStore) bit.toNat).length
    simp [putAt, hcursor]
  rintro b rfl
  refine (hs_add C lengthCounter v2 _ (by decide) ?_).mono le_rfl ?_
  · simpa (config := {decide := true}) [DS.put, DS.set, hc.two] using hcap
  rintro b rfl
  simp (config := {decide := true}) [frameStep, DS.put, DS.set, putAt, hcursor, hc.two,
    List.append_assoc]

end NearQuarticWires.StageMain.Compact
