import Proof.Quartic.StageCert.ReadTest

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary

/-- `sec:algorithm`, paper/paper.tex: write one framed
certification bit from the acceptance register. -/
def finishTest : St VV MM :=
  .seq (.op (.emit true))
    (.seq (.ite (.eq testAccept vZ) (.op (.emit false)) (.op (.emit true)))
      (.op (.emit false)))

/-- `sec:algorithm`, paper/paper.tex: the output of the physical
bit writer is exactly the framed strict-test result. -/
theorem finishTest_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (b : Bool)
    (ha : a.env testAccept = if b then 1 else 0) :
    Hs C finishTest a 6 (fun d => d.out = a.out ++ frame [b]) := by
  unfold finishTest
  refine Hs.seq (t1 := 1) (t2 := 4) (hs_emit C true a) (fun d hd => ?_)
  subst d
  cases b with
  | false =>
    have ht : Cnd.eval { a with out := a.out ++ [true] } (.eq testAccept vZ) = true := by
      simp [Cnd.eval, ha, hc.z]
    refine Hs.seq (t1 := 2) (t2 := 1)
      (Hs.iteT (by norm_num [Cnd.wf, testAccept, vZ]) ht (hs_emit C false _)) (fun e he => ?_)
    subst e
    refine (hs_emit C false _).mono le_rfl ?_
    intro d hd
    subst d
    simp [frame, List.append_assoc]
  | true =>
    have ht : Cnd.eval { a with out := a.out ++ [true] } (.eq testAccept vZ) = false := by
      simp [Cnd.eval, ha, hc.z]
    refine Hs.seq (t1 := 2) (t2 := 1)
      (Hs.iteF (by norm_num [Cnd.wf, testAccept, vZ]) ht (hs_emit C true _)) (fun e he => ?_)
    subst e
    refine (hs_emit C false _).mono le_rfl ?_
    intro d hd
    subst d
    simp [frame, List.append_assoc]

end NearQuarticWires.StageCert
