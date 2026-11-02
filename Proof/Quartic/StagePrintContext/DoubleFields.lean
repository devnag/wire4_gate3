import Proof.Quartic.StagePrintContext.Framing
import Proof.Gates.Cells.Run

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageRecovery.OutputFrame

/-- `lem:print`, paper/paper.tex: the affine
header field has one actual internal frame and one field-delimiter frame. -/
def doubleFramedFields (fields : List (Fin VV)) : St VV MM :=
  framedProgram (framedProgram (StagePrint.Header.emitHeaderFields fields))

/-- `lem:print` and `prop:time`, paper/paper.tex: the two new marker layers leave all earlier fields
unchanged and retain every nonscratch affine-header register. -/
theorem doubleFramedFields_run (C : Ctx) (fields : List (Fin VV)) (a : DS VV MM)
    (hc : Cst a) (hv : Valid C a) (hW : 3≤C.Wd)
    (hf : ∀field∈fields,field∉StagePrint.Header.headerEmitScratch) :
    Hs C (doubleFramedFields fields) a
      (9*StagePrint.Header.headerEmitCost (fields.map a.env)+8) (fun b=>
        b.out=a.out++frame (frame ((fields.map a.env).flatMap NearCubicWires.RepairRepresentation.natWord)) ∧
        b.ip=a.ip ∧b.ram=a.ram ∧b.rc=a.rc ∧
        (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧Cst b ∧Valid C b ∧
        Fr a b StagePrint.Header.headerEmitScratch) := by
  let clean : DS VV MM:={a with out:=[]}
  have hclean : Valid C clean:=valid_output hv []
  have er:=StagePrint.Header.emitHeaderFields_run C fields clean ⟨hc.z,hc.one,hc.two⟩ (by omega) hf
    (by intro field _hfield;exact valid_nat_emission hclean hW field)
  obtain ⟨b,n,he,hn,hout,hrest,hbc,hfr⟩:=er
  change n≤StagePrint.Header.headerEmitCost (fields.map a.env) at hn
  have hframe:=doubleFrame_afterPrefix he rfl a.out
  have hstart : {clean with out:=a.out}=a := by cases a;rfl
  rw [hstart] at hframe
  let last : DS VV MM:={b with out:=a.out++frame (frame b.out)}
  have hvalid:=hframe.valid (by omega) (callee_hB C) hv
  refine ⟨last,9*n+8,hframe,by omega,?_,?_,?_,?_,?_,⟨hbc.z,hbc.one,hbc.two⟩,hvalid,hfr⟩
  · simpa only [last,clean,List.nil_append] using congrArg (fun bits=>a.out++frame (frame bits)) hout
  · exact congrArg (fun q=>q.1) hrest
  · exact congrArg (fun q=>q.2.1) hrest
  · exact congrArg (fun q=>q.2.2.1) hrest
  · exact congrArg (fun q=>(q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) hrest

end NearQuarticWires.StagePrintContext
