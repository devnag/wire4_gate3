import Proof.Quartic.StageTupleSetupCold.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open StageTuple

namespace Helpers

def finishSteps (F : Helpers) (r : TermCutRequest) : ℕ :=
  (1000*((natWord r.stackWidth).length+1)+1+(2*F.widthBudget r.stackWidth+2))+1+
  ((1000*((frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)).length+1)+1+
    (2*F.rowBudget (rowRequest r)+2))+1+
  ((1000*((natWord (r.stackWidth+1)++intWord 0).length+1)+1+
    (2*F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) 0)+2))+1+
  ((1000*((natWord (r.stackWidth+1)++intWord 1).length+1)+1+
    (2*F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) 1)+2))+1+
    100000*(r.word.length+r.setupStructuralMagnitude))))

/-- `lem:print`, paper/paper.tex: four
actual small ordinary calls return their genuine replies on disjoint
private banks. The complete prepared formatter consumes those replies
and retained original sources; no helper output or decoded input is
assumed, and the complete Terms bytes are copied exactly once. -/
theorem finish_run (F : Helpers) (r : TermCutRequest) (σ : WState F.ns 8)
    (hr : Ready F r σ) (hcold : ∀i,(∀j : Fin 24,i≠F.data j)→σ.st i=[]) :
    ∃τ,WXExec (capacity r) F.finish σ τ (F.finishSteps r) ∧
      τ.st (F.data 16)=frame r.preparedWord := by
  have cw : ∀j,σ.st (F.widthBank j)=[]:=fun j=>hcold _
    (fun i=>(StageTupleSetup.BankLayout.widthBank_ne_data j i))
  have cr : ∀j,σ.st (F.rowBank j)=[]:=fun j=>hcold _
    (fun i=>(StageTupleSetup.BankLayout.rowBank_ne_data j i))
  have cz : ∀j,σ.st (F.zeroBank j)=[]:=fun j=>hcold _
    (fun i=>(StageTupleSetup.BankLayout.zeroBank_ne_data j i))
  have co : ∀j,σ.st (F.oneBank j)=[]:=fun j=>hcold _
    (fun i=>(StageTupleSetup.BankLayout.twoBank_ne_data j i))
  obtain ⟨a,wa,ew,dw,hw⟩:=F.widthStage_run (capacity r) r σ (hr.loaded 6) cw
    hr.heads hr.registers hr.widthRuler (by unfold capacity;omega)
  have ha:=hr.of_docked dw (fun i j=>StageTupleSetup.BankLayout.widthBank_ne_data i j)
  have cra:=cold_after_docked dw StageTupleSetup.BankLayout.width_row_ne cr
  have cza:=cold_after_docked dw StageTupleSetup.BankLayout.width_zero_ne cz
  have coa:=cold_after_docked dw StageTupleSetup.BankLayout.width_two_ne co
  obtain ⟨b,wb,er,dr,hrow⟩:=F.rowStage_run (capacity r) r a (ha.loaded 3) cra
    ha.heads ha.registers ha.rowRuler (by unfold capacity;omega)
  have hb:=ha.of_docked dr (fun i j=>StageTupleSetup.BankLayout.rowBank_ne_data i j)
  have czb:=cold_after_docked dr StageTupleSetup.BankLayout.row_zero_ne cza
  have cob:=cold_after_docked dr StageTupleSetup.BankLayout.row_two_ne coa
  have hwb : b.st (F.widthBank F.width.program.outputTape)=frame (natWord (r.stackWidth+1)) :=
    ((dr.other _ (fun i=>(StageTupleSetup.BankLayout.width_row_ne _ i).symm)).1).trans hw
  obtain ⟨c,wc,ez,dz,hzero⟩:=F.coefficientStage_run false (capacity r) r b hwb czb
    hb.heads hb.registers hb.zeroRuler (by
      change 2*(natWord (r.stackWidth+1)++intWord 0).length+10≤capacity r
      unfold capacity
      omega)
  have hc:=hb.of_docked dz (fun i j=>StageTupleSetup.BankLayout.zeroBank_ne_data i j)
  have coc:=cold_after_docked dz StageTupleSetup.BankLayout.zero_two_ne cob
  have hwc : c.st (F.widthBank F.width.program.outputTape)=frame (natWord (r.stackWidth+1)) :=
    ((dz.other _ (fun i=>(StageTupleSetup.BankLayout.width_zero_ne _ i).symm)).1).trans hwb
  have hrc : c.st (F.rowBank F.row.program.outputTape)=frame (natWord (r.rowDimension+1)) :=
    ((dz.other _ (fun i=>(StageTupleSetup.BankLayout.row_zero_ne _ i).symm)).1).trans hrow
  obtain ⟨d,wd,eo,do_,hone⟩:=F.coefficientStage_run true (capacity r) r c hwc coc
    hc.heads hc.registers hc.oneRuler (by
      change 2*(natWord (r.stackWidth+1)++intWord 1).length+10≤capacity r
      unfold capacity
      omega)
  have hd:=hc.of_docked do_ (fun i j=>StageTupleSetup.BankLayout.twoBank_ne_data i j)
  have hwd : d.st (F.widthBank F.width.program.outputTape)=frame (natWord (r.stackWidth+1)) :=
    ((do_.other _ (fun i=>(StageTupleSetup.BankLayout.width_two_ne _ i).symm)).1).trans hwc
  have hrd : d.st (F.rowBank F.row.program.outputTape)=frame (natWord (r.rowDimension+1)) :=
    ((do_.other _ (fun i=>(StageTupleSetup.BankLayout.row_two_ne _ i).symm)).1).trans hrc
  have hzd : d.st (F.zeroBank F.coefficient.program.outputTape)=
      (CoefficientRequest.mk (r.stackWidth+1) 0).output :=
    ((do_.other _ (fun i=>(StageTupleSetup.BankLayout.zero_two_ne _ i).symm)).1).trans hzero
  have ef:=StageTuplePreparedOutput.preparedOutputProgram_spec (capacity r) F.preparedPorts
    (regs 4 (by decide)) r d (hd.loaded 2) (hd.loaded 3) hd.context (hd.loaded 1)
    hwd hzd hone hrd hd.degree hd.output (fun _=>hd.heads _) (fun _=>hd.registers _)
    (by unfold StageTupleSetup.preparedOutputMagnitude capacity;omega)
  refine ⟨d.sets (F.data 16) (frame r.preparedWord),
    ew.seq (er.seq (ez.seq (eo.seq (WXExec.wm ef)))),?_⟩
  simp only [WState.sets_st,Function.update_self]

end Helpers

end NearQuarticWires.StageTupleSetupCold
