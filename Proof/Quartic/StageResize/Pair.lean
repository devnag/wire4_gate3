import Proof.Quartic.StageLift.FrameRead

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

def copied : Fin VV := 20
def targetWidth : Fin VV := 21

/-- `lem:print`, paper/paper.tex: emit the actual
payload bit with one marker, without decoding a field value. -/
def pairProgram : St VV MM :=
  .seq (.op (.emit true))
    (.ite (.eq t1 v1) (.op (.emit true)) (.op (.emit false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: both marker and payload emissions are physical steps. -/
theorem pairProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (bit : Bool)
    (hb : a.env t1 = bit.toNat) :
    Hs C pairProgram a 4 (fun b => b = {a with out := a.out ++ [true, bit]}) := by
  unfold pairProgram
  refine Hs.seq (t1 := 1) (t2 := 2) (hs_emit C true a) ?_
  rintro b rfl
  cases bit with
  | false =>
      refine Hs.iteF (show t1 ≠ v1 by decide) (by simp [Cnd.eval, hb, hc.one]) ?_
      refine (hs_emit C false _).mono le_rfl ?_
      rintro b rfl
      simp only [List.append_assoc]
      rfl
  | true =>
      refine Hs.iteT (show t1 ≠ v1 by decide) (by simp [Cnd.eval, hb, hc.one]) ?_
      refine (hs_emit C true _).mono le_rfl ?_
      rintro b rfl
      simp only [List.append_assoc]
      rfl

end NearQuarticWires.StageResize
