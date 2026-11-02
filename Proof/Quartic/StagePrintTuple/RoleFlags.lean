import Proof.Quartic.StagePrintTuple.RoleCompute

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex:
one physically stored corner flag is emitted as its literal raw bit,
rather than as an additional natural-codec field. -/
def emitRoleFlag (x : Fin VV) : St VV MM :=
  .ite (.eq x v1) (.op (.emit true)) (.op (.emit false))

/-- `lem:print` and `prop:time`, paper/paper.tex: the raw-flag writer is an actual binary
branch and leaves every scalar and source cursor unchanged. -/
theorem emitRoleFlag_spec (C : Ctx) (x : Fin VV) (hx : x ≠ v1)
    (a : DS VV MM) (hc : Cst a) :
    Hs C (emitRoleFlag x) a 3 (fun b =>
      b = {a with out := a.out ++ [decide (a.env x = 1)]}) := by
  unfold emitRoleFlag
  by_cases h : a.env x = 1
  · refine (Hs.iteT (c:=.eq x v1) hx
      (by simp [Cnd.eval,h,hc.one]) (hs_emit C true a)).mono (by omega) ?_
    intro b hb
    simpa only [h,decide_true] using hb
  · refine (Hs.iteF (c:=.eq x v1) hx
      (by simp [Cnd.eval,h,hc.one]) (hs_emit C false a)).mono (by omega) ?_
    intro b hb
    simpa only [h,decide_false] using hb

/-- `lem:print`, paper/paper.tex:
the final three affine flags follow the two selected walk coordinates. -/
def emitRoleFlags : St VV MM :=
  .seq (emitRoleFlag StagePrint.Header.leftCorner)
    (.seq (emitRoleFlag StagePrint.Header.rightCorner)
      (emitRoleFlag StagePrint.Header.transpose))

/-- `lem:print` and `prop:time`, paper/paper.tex: all three flag branches are charged, with
exact bit order and no changes to the retained source or scalar fields. -/
theorem emitRoleFlags_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) :
    Hs C emitRoleFlags a 11 (fun b =>
      b = {a with out := a.out ++
        [decide (a.env StagePrint.Header.leftCorner = 1),
         decide (a.env StagePrint.Header.rightCorner = 1),
         decide (a.env StagePrint.Header.transpose = 1)]}) := by
  unfold emitRoleFlags
  refine Hs.seq (t2:=7)
    (emitRoleFlag_spec C StagePrint.Header.leftCorner (by decide) a hc) ?_
  rintro b hb
  have bc : Cst b := by rw [hb];exact ⟨hc.z,hc.one,hc.two⟩
  refine Hs.seq (t2:=3)
    (emitRoleFlag_spec C StagePrint.Header.rightCorner (by decide) b bc) ?_
  rintro d hd
  have dc : Cst d := by rw [hd];exact ⟨bc.z,bc.one,bc.two⟩
  refine (emitRoleFlag_spec C StagePrint.Header.transpose (by decide) d dc).mono le_rfl ?_
  intro out ho
  rw [ho,hd,hb]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

end NearQuarticWires.StageTuple
