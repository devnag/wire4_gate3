import Proof.Quartic.StagePrintContext.CallField
import Proof.Quartic.StagePrintContext.CountsField
import Proof.Quartic.StagePrintContext.GeometryField
import Proof.Quartic.StagePrint.ContextTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCertTests StagePrint.Header

/-- `lem:print`, paper/paper.tex: one actual
common context is emitted before either consumer starts its walk loop. -/
def contextBody : St VV MM :=
  .seq emitCallField (.seq emitHeaderField (.seq emitCountsField
    (.seq emitGeometryField (emitLiteral (List.replicate 7 false)))))

/-- `prop:time`, paper/paper.tex: every actual
source/header/census/geometry write and empty-field marker is charged. -/
noncomputable def bodySteps {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) (width : ℕ) : ℕ :=
  40*((callWord r.call).length+1)+headerFieldCost (StagePrint.Context.header r) width+
    countsFieldCost width+(3*fieldClock 4 width+2)+15+4

/-- `lem:print` and `prop:time`, paper/paper.tex: all eleven context fields arise from the retained
original call, public parameter records and witness. The literal order
and nested marker structure agree with the common physical loader. -/
theorem contextBody_run {B1 B2 : ℕ} (C : Ctx) (r : PreparedScheduleRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : Valid C a)
    (hd : HeaderSourceData (StagePrint.Context.header r) a)
    (hlen : a.env StageMain.CallSkip.lengthCounter=(callWord r.call).length)
    (hMin : 5≤C.Wd) (hWd : r.call.n+3≤C.Wd)
    (hcap : 4*(r.call.n+1)^2+r.call.n+20<2^C.Wd) :
    Hs C contextBody a (bodySteps r C.Wd) (fun z=>z.out=a.out++StagePrint.Context.word r) := by
  have hfit : (callWord r.call).length<2^C.Wd := by rw [←hlen];exact ha.env_lt _
  unfold contextBody
  apply Hx.hs
  refine Hs.then (emitCallField_run C (StagePrint.Context.header r) a hc ha hd hlen hfit (by omega))
    (fun b ⟨bo,bi,br,bs,bc,bv⟩ n1 hn1=>?_)
  have bdata : HeaderSourceData (StagePrint.Context.header r) b :=
    ⟨by rw [br];exact hd.originalCall,by rw [br];exact hd.scalarFields,by rw [br];exact hd.witnessBits⟩
  refine Hs.then (emitHeaderField_run C (StagePrint.Context.header r) b bc bv bdata hWd hcap)
    (fun d ⟨do_,dh,dr,di,ds,dc,dv⟩ n2 hn2=>?_)
  have dpar : d.ram StageLift.parameterStore=StageLift.parameterScalars r.selected.1 := by
    rw [dr,br]
    exact hd.scalarFields
  refine Hs.then (emitCountsField_run C r.call (StagePrint.Context.header r).prepared d dc dv dpar hMin)
    (fun e ⟨eo,ei,er,es,ec,ev,efr⟩ n3 hn3=>?_)
  have eh : BaseHeaderData (StagePrint.Context.header r) e := by
    constructor
    · rw [efr arity (by decide)];exact dh.n
    · rw [efr Lin (by decide)];exact dh.sourceWidth
    · rw [efr Lout (by decide)];exact dh.targetWidth
    · rw [efr blockCount (by decide)];exact dh.r
    · rw [efr blockWidth (by decide)];exact dh.b
    · rw [efr syndromeWidth (by decide)];exact dh.s
    · rw [efr translation (by decide)];exact dh.translation
  refine Hs.then (emitGeometryField_run C (StagePrint.Context.header r) e ec ev eh (by omega))
    (fun f ⟨fo,_fi,_fr,_fs,_fc,_fv⟩ n4 hn4=>?_)
  refine Hs.last (emitLiteral_run C (List.replicate 7 false) f) (fun z hz n5 hn5=>?_)
  refine ⟨?_,?_⟩
  · rw [hz,fo,eo,do_,bo]
    simp only [StagePrint.Context.word,Top.loadRec,StagePrint.Context.countsWord,
      StagePrint.Context.geometryWord,StagePrint.Context.header,List.append_assoc]
    rfl
  · change n5≤2*7+1 at hn5
    change n1≤40*((callWord r.call).length+1) at hn1
    unfold bodySteps
    omega

end NearQuarticWires.StagePrintContext
