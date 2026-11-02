import Proof.Quartic.StageMain.CallSkipCall
import Proof.Quartic.StageLift.FrameRead

/-!
# Reading the dispatched call prefix of a stage word

`sec:algorithm`, paper/paper.tex, and `prop:time`: on a dispatched stage word the true tag is followed
by the original finite call. The measured call length excludes this
tag and every later parameter or certificate field.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

def scanTaggedCall : St VV MM := .seq (.op (.rdI t0)) scanCall

theorem scanTaggedCall_run (C : Ctx) (c : Call) (suffix : List Bool) (a : DS VV MM)
    (hc : Cst a) (hin : C.inp.drop a.ip = true :: (callWord c ++ suffix))
    (hW : (callWord c).length + 2 ≤ C.Wd) :
    Hs C scanTaggedCall a (3000 * ((callWord c).length + 1) ^ 3 + 4) (fun b =>
      b.ip = a.ip + 1 + (callWord c).length ∧
      b.env lengthCounter = (callWord c).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b gateListScratch) := by
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 3000 * ((callWord c).length + 1) ^ 3 + 2)
    (StageLift.readInputBit_spec C t0 a true (callWord c ++ suffix) hin) ?_)
    (by omega) (fun _ h => h)
  rintro b rfl
  let b : DS VV MM := { a.set t0 1 with ip := a.ip + 1 }
  have hf : Fr a b gateListScratch := Fr.set a _ (by decide)
  have hbc : Cst b := Cst.of_fr hc hf (by decide)
  have hbinput : C.inp.drop b.ip = callWord c ++ suffix := by
    change C.inp.drop (a.ip + 1) = _
    rw [← List.drop_drop, hin]
    rfl
  refine (scanCall_run C c suffix b hbc hbinput hW).mono le_rfl ?_
  intro d ⟨hdip, hdlen, hdrest, hdc, hdfr⟩
  exact ⟨hdip, hdlen, hdrest, hdc, hf.trans hdfr⟩

end NearQuarticWires.StageMain.CallSkip
