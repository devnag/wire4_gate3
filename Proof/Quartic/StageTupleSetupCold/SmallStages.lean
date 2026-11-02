import Proof.Quartic.StageTupleSetupCold.CallAfter

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open StageTuple

namespace Helpers

/-- `lem:print`, paper/paper.tex: the
literal original-width codec is framed and passed to the actual
width helper in its own one-shot cold bank. -/
noncomputable def widthStage (F : Helpers) : WMX F.ns 8 :=
  .seq (.wm (StageTupleSetup.frameNaturalProgram F.widthPair (regs 3 (by decide))))
    (.machZ F.width.program.machine F.widthBank (F.data 20))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual width reply follows
from one physical input-framing pass and one real ordinary call. -/
theorem widthStage_run (F : Helpers) (cap : ℕ) (r : TermCutRequest) (σ : WState F.ns 8)
    (hs : σ.st (F.data 6)=natWord r.stackWidth)
    (hcold : ∀j,σ.st (F.widthBank j)=[])
    (hh : ∀i,σ.sh i=0) (hz : ∀i,σ.val i=0)
    (hpad : σ.st (F.data 20)=List.replicate (F.widthBudget r.stackWidth) false)
    (hcap : 2*(natWord r.stackWidth).length+2≤cap) :
    ∃τ tout,WXExec cap F.widthStage σ τ
      (1000*((natWord r.stackWidth).length+1)+1+(2*F.widthBudget r.stackWidth+2)) ∧
      Docked F.widthBank σ τ (fun _=>0) tout ∧
      τ.st (F.widthBank F.width.program.outputTape)=frame (natWord (r.stackWidth+1)) := by
  have he:=StageTupleSetup.frameNaturalProgram_spec cap F.widthPair (regs 3 (by decide))
    r.stackWidth σ hs (hh _) (hcold _) (hh _) (fun i=>hz _) hcap
  exact call_after_input F.width r.stackWidth cap F.widthBank
    StageTupleSetup.BankLayout.widthBank_injective F.widthInput rfl (F.data 20)
    (fun j=>StageTupleSetup.BankLayout.widthBank_ne_data j 20)
    _ _ σ he hcold (fun j=>hh _) hpad (hh _)

/-- `lem:print`, paper/paper.tex: the
actual retained header is passed to the cold row-count helper with
its original inner frame and a physically written ordinary input frame. -/
noncomputable def rowStage (F : Helpers) : WMX F.ns 8 :=
  .seq (.wm (StageTupleSetup.frameRetainedProgram F.rowPair (regs 2 (by decide))))
    (.machZ F.row.program.machine F.rowBank (F.data 21))

/-- `lem:print` and `prop:time`, paper/paper.tex: the genuine small header produces
the exact row count while preserving all external retained data. -/
theorem rowStage_run (F : Helpers) (cap : ℕ) (r : TermCutRequest) (σ : WState F.ns 8)
    (hs : σ.st (F.data 3)=frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord))
    (hcold : ∀j,σ.st (F.rowBank j)=[])
    (hh : ∀i,σ.sh i=0) (hz : ∀i,σ.val i=0)
    (hpad : σ.st (F.data 21)=List.replicate (F.rowBudget (rowRequest r)) false)
    (hcap : 2*(frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)).length+2≤cap) :
    ∃τ tout,WXExec cap F.rowStage σ τ
      (1000*((frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)).length+1)+1+
        (2*F.rowBudget (rowRequest r)+2)) ∧
      Docked F.rowBank σ τ (fun _=>0) tout ∧
      τ.st (F.rowBank F.row.program.outputTape)=frame (natWord (r.rowDimension+1)) := by
  have he:=StageTupleSetup.frameRetainedProgram_spec cap F.rowPair (regs 2 (by decide))
    ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord) σ hs (hh _)
    (hcold _) (hh _) (fun i=>hz _) hcap
  exact call_after_input F.row (rowRequest r) cap F.rowBank
    StageTupleSetup.BankLayout.rowBank_injective F.rowInput rfl (F.data 21)
    (fun j=>StageTupleSetup.BankLayout.rowBank_ne_data j 21)
    _ _ σ he hcold (fun j=>hh _) hpad (hh _)

end Helpers

end NearQuarticWires.StageTupleSetupCold
