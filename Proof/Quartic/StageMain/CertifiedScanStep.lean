import Proof.Quartic.StageLift.FrameRead
import Proof.Quartic.StageMain.Totals

/-!
# Streaming certificate counts

Step 4 of `sec:algorithm`, paper/paper.tex, traverses
certified columns. The framed certificate is read without a second
certificate table; two counters record all columns and the true flags.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

def certificateScratch : List (Fin VV) := [t0, t1, certifiedCount, columnCounter]

def countCertificateBody : St VV MM :=
  .seq (.op (.rdI t1)) (.seq (.op (.add certifiedCount t1))
    (.seq (.op (.inc columnCounter)) (.op (.rdI t0))))

def certificateStep (a : DS VV MM) (bit marker : Bool) : DS VV MM :=
  { ((a.set t1 bit.toNat).set certifiedCount (a.env certifiedCount + bit.toNat)).set
      columnCounter (a.env columnCounter + 1) with
    env := Function.update
      (((a.set t1 bit.toNat).set certifiedCount (a.env certifiedCount + bit.toNat)).set
        columnCounter (a.env columnCounter + 1)).env t0 marker.toNat
    ip := a.ip + 2 }

theorem certificateStep_fr (a : DS VV MM) (bit marker : Bool) :
    Fr a (certificateStep a bit marker) certificateScratch := by
  intro y hy
  simp only [certificateScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [certificateStep, DS.set, Function.update_of_ne hy.1,
    Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.1,
    Function.update_of_ne hy.2.2.2]

theorem countCertificateBody_run (C : Ctx) (a : DS VV MM) (bit marker : Bool)
    (rest : List Bool) (hin : C.inp.drop a.ip = bit :: marker :: rest)
    (hcount : a.env certifiedCount + bit.toNat < 2 ^ C.Wd)
    (hindex : a.env columnCounter + 1 < 2 ^ C.Wd) :
    Hs C countCertificateBody a 7 (fun b => b = certificateStep a bit marker) := by
  unfold countCertificateBody
  refine Hs.seq (t2 := 5) (readInputBit_spec C t1 a bit (marker :: rest) hin) ?_
  rintro b rfl
  refine Hs.seq (t2 := 3) (hs_add C certifiedCount t1 _ (by decide) ?_) ?_
  · simpa [DS.set_env_ne _ _ (by decide : certifiedCount ≠ t1)] using hcount
  rintro b rfl
  refine Hs.seq (t2 := 1) (hs_inc C columnCounter _ ?_) ?_
  · simpa (config := {decide := true}) [DS.set] using hindex
  rintro b rfl
  have hnext : C.inp.drop (a.ip + 1) = marker :: rest := by
    rw [← List.drop_drop, hin]
    rfl
  refine (readInputBit_spec C t0 _ marker rest hnext).mono le_rfl ?_
  rintro b rfl
  simp (config := {decide := true}) [certificateStep, DS.set]

end NearQuarticWires.StageMain.Controller
