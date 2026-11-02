import Proof.Quartic.StageNativeRowCount.Program

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: no supplied
metadata decoder, count producer or arithmetic-value callee is used. -/
noncomputable def rowCountCallee : Callee :=
  ⟨Empty, fun e=>e.elim, fun e=>e.elim, fun e=>e.elim,
    wordFunction_of_wmx (WMX.skip : WMX 1 0) 1 (by decide) (fun _=>0) (fun e=>e.elim)⟩

/-- `prop:time`, paper/paper.tex: the exact cold
ordinary cost includes all header scans, bounded binary arithmetic,
scalar output framing, initialization and final head reset. -/
noncomputable def Request.budget (r : Request) : ℕ :=
  langBudget rowCountCallee rowCountSizes VV MM r.word r.sourceClock

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual existing framed header bytes produce exactly
the framed native row-field count on a genuine cold ordinary machine. -/
noncomputable def rowCountWordFunction :
    WordFunction Request Request.word Request.output Request.budget :=
  wordFunction_of_lang Request.word Request.output rowCountCallee rowCountSizes
    program Request.sourceClock (by
      intro r
      obtain ⟨b,k,he,hk,ho⟩:=program_spec
        (ctxOf rowCountCallee rowCountSizes r.word) r rfl r.setup_lower
      exact ⟨b,k,he,ho,hk⟩) (by
      intro r
      have hh:=r.setup_lower
      have ht : 1≤(r.header.call.n+1)^2 := Nat.pow_pos (Nat.succ_pos _)
      omega)

end NearQuarticWires.StageNativeRowCount
