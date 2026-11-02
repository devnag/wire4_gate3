import Proof.Quartic.StagePrintTuple.SetupContract

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup.OneShotCore

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.LocalBitMultitape
open NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual small helper runs once on its internally
constructed cold tape bank. Its proved finite blank ruler is private
ordinary workspace, never a caller-supplied allocator/provider premise. -/
theorem run {Request : Type} {input output : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input output budget) (req : Request) (cap : ℕ)
    (bank : Fin f.program.tapeCount→Fin (ns+1)) (hb : Function.Injective bank)
    (ruler : Fin (ns+1)) (hbr : ∀j,bank j≠ruler) (σ : WState ns nr)
    (hin : ∀j,σ.st (bank j)=f.program.inputTapes (input req) j)
    (hh : ∀j,σ.sh (bank j)=0)
    (hpad : σ.st ruler=List.replicate (budget req) false) (hrh : σ.sh ruler=0) :
    ∃τ tout,WXExec cap (.machZ f.program.machine bank ruler) σ τ (2*budget req+2) ∧
      Docked bank σ τ (fun _=>0) tout ∧ τ.st (bank f.program.outputTape)=output req := by
  obtain ⟨actual,hr,ho⟩:=f.realizes req
  have hi : (fun j=>σ.st (bank j))=f.program.inputTapes (input req) := funext hin
  rw [←hi] at hr
  obtain ⟨τ,he,hd⟩:=WXExec.machZ_run (cap:=cap) hb hbr σ hr hh hpad hrh le_rfl
  exact ⟨τ,actual.final.tapes,he,hd,by rw [hd.st,ho]⟩

end NearQuarticWires.StageTupleSetup.OneShotCore
