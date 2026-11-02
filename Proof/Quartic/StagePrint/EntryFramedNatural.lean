import Proof.Quartic.StageLift.OutputPrefix
import Proof.Quartic.StageRecovery.NaturalPrint

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a literal
Tuple scalar field is one frame around its canonical natural codec. -/
def emitFramedVariable (x : Fin VV) : St VV MM :=
  StageRecovery.OutputFrame.framedProgram (StageRecovery.emitVariable x)

/-- `lem:print`, paper/paper.tex: physical
scalar framing appends after earlier fields, preserves all source
streams and pays every marker without a numeric-value loop. -/
theorem emitFramedVariable_run (C : Ctx) (x : Fin VV) (a : DS VV MM) (hc : Cst a)
    (hx : x≠t3) (hW : 2≤C.Wd)
    (hfit : natBitLength (a.env x)+2<2^C.Wd) :
    Hs C (emitFramedVariable x) a (3*(40*natBitLength (a.env x)+42)+2) (fun b =>
      b.out=a.out++frame (natWord (a.env x)) ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [t3,t5,t6,t7,t8,t9]) := by
  obtain ⟨b,n,he,hn,bo,br,bc,bfr⟩ :=
    StageRecovery.emitVariable_spec C {a with out:=[]} ⟨hc.z,hc.one,hc.two⟩ x hx hW hfit
  have hf:=StageLift.framedProgram_afterPrefix he rfl a.out
  have ha : { {a with out:=[]} with out:=a.out}=a := by cases a;rfl
  rw [ha] at hf
  change n≤40*natBitLength (a.env x)+42 at hn
  refine ⟨{b with out:=a.out++frame b.out},3*n+2,hf,by omega,?_,br,⟨bc.z,bc.one,bc.two⟩,bfr⟩
  simp only [bo,List.nil_append]

end NearQuarticWires.StagePrint.EntryFormat
