import Proof.Quartic.StageLift.OutputPrefix
import Proof.Quartic.StagePrint.HeaderEmit
import Proof.Gates.Dispatch.Print

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageRecovery.OutputFrame

/-- `lem:print`, paper/paper.tex: replacing
only previously emitted bytes leaves every source-validity fact intact. -/
theorem valid_output {V M : ℕ} {C : Ctx} {a : DS V M}
    (ha : Valid C a) (output : List Bool) : Valid C {a with out:=output} :=
  ⟨ha.env_lt,ha.ip_le,ha.ram_lt,ha.rc_le,ha.kin_le,ha.kout_le,ha.kc_le⟩

/-- `lem:print`, paper/paper.tex: two real
framing transformations retain every already written context field;
only the new field gains its two required frame layers. -/
theorem doubleFrame_afterPrefix {V M : ℕ} {C : Ctx} {s : St V M}
    {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (ha : a.out=[]) (front : List Bool) :
    Ex C (framedProgram (framedProgram s)) {a with out:=front}
      {b with out:=front++frame (frame b.out)} (9*n+8) := by
  have hfirst:=framedProgram_spec h
  have hsecond:=StageLift.framedProgram_afterPrefix hfirst
    (by simp [markedState,markedBits,ha]) front
  have hcost : 3*(3*n+2)+2=9*n+8 := by omega
  simpa only [markedState,markedBits,ha,List.flatMap_nil,framedState,hcost] using hsecond

/-- `prop:time`, paper/paper.tex: each runtime
natural value is serialized at its actual binary length in a valid state. -/
theorem valid_nat_emission {C : Ctx} {a : DS VV MM} (ha : Valid C a)
    (hW : 3≤C.Wd) (field : Fin VV) : natBitLength (a.env field)+2<2^C.Wd := by
  have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_of_lt (ha.env_lt field) (by omega)
  have hp:=NearCubicGates.Close.Dispatch.wd_small C.Wd hW
  omega

/-- `lem:print`, paper/paper.tex: an actual
finite list of loaded scalar registers contributes one framed field. -/
def framedFields (fields : List (Fin VV)) : St VV MM :=
  framedProgram (StagePrint.Header.emitHeaderFields fields)

/-- `lem:print` and `prop:time`, paper/paper.tex: a framed scalar field is physically appended after
all previous context fields, preserving every nonscratch source value. -/
theorem framedFields_run (C : Ctx) (fields : List (Fin VV)) (a : DS VV MM)
    (hc : Cst a) (hv : Valid C a) (hW : 3≤C.Wd)
    (hf : ∀field∈fields,field∉StagePrint.Header.headerEmitScratch) :
    Hs C (framedFields fields) a
      (3*StagePrint.Header.headerEmitCost (fields.map a.env)+2) (fun b=>
        b.out=a.out++frame ((fields.map a.env).flatMap NearCubicWires.RepairRepresentation.natWord) ∧
        b.ip=a.ip ∧b.ram=a.ram ∧b.rc=a.rc ∧
        (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧Cst b ∧Valid C b ∧
        Fr a b StagePrint.Header.headerEmitScratch) := by
  let clean : DS VV MM:={a with out:=[]}
  have hclean : Valid C clean:=valid_output hv []
  have er:=StagePrint.Header.emitHeaderFields_run C fields clean ⟨hc.z,hc.one,hc.two⟩ (by omega) hf
    (by intro field _hfield;exact valid_nat_emission hclean hW field)
  obtain ⟨b,n,he,hn,hout,hrest,hbc,hfr⟩:=er
  change n≤StagePrint.Header.headerEmitCost (fields.map a.env) at hn
  have hframe:=StageLift.framedProgram_afterPrefix he rfl a.out
  have hstart : {clean with out:=a.out}=a := by cases a;rfl
  rw [hstart] at hframe
  let last : DS VV MM:={b with out:=a.out++frame b.out}
  have hvalid:=hframe.valid (by omega) (callee_hB C) hv
  refine ⟨last,3*n+2,hframe,by omega,?_,?_,?_,?_,?_,⟨hbc.z,hbc.one,hbc.two⟩,hvalid,hfr⟩
  · simpa only [last,clean,List.nil_append] using congrArg (fun bits=>a.out++frame bits) hout
  · exact congrArg (fun q=>q.1) hrest
  · exact congrArg (fun q=>q.2.1) hrest
  · exact congrArg (fun q=>q.2.2.1) hrest
  · exact congrArg (fun q=>(q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) hrest

end NearQuarticWires.StagePrintContext
