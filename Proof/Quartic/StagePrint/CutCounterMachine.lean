import Proof.Quartic.StagePrint.CutCounterRun

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.CutCounter

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Expand.PolyTab

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete ordinary clock includes the physical
count scan, binary count writer and final head restoration. -/
def Request.budget (r : Request) : ℕ := 2*r.clock+2

/-- `lem:print`, paper/paper.tex: the actual
cold equality-stream counter emits the canonical framed count
without receiving a count or source-length oracle. -/
noncomputable def counterWordFunction :
    WordFunction Request Request.word (fun r=>frame (natWord r.cuts.length)) Request.budget :=
  wordFunction_of_ideal program (15 : Fin 16) (by decide) Request.capacity Request.lens
    Request.clock (fun _=>le_rfl) (fun r=>⟨rfl,program_run r⟩)

end NearQuarticWires.StagePrint.CutCounter
