import Proof.Quartic.StageCert.PopulationPrefix
import Proof.Quartic.Program.Stages

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- `def:mask` and witness (W2), paper/paper.tex: an internal finite-source population request retains the
complete original two-circuit call, four physically computed point codes
and the actual finite witness bits selecting original occurrences. -/
structure PopulationRequest where
  call : Call
  arity_le_call : call.n ≤ (callWord call).length
  offset : ℕ
  corners : Fin 4 → ℕ
  witness : List Bool
  selection_fits : offset + call.first.gates.length + call.second.gates.length ≤ witness.length

/-- `def:mask` and `prop:time`, paper/paper.tex: the internal request's literal source contains the original
call, binary offset and four point codes, then the framed actual witness. -/
def PopulationRequest.word (r : PopulationRequest) : List Bool :=
  callWord r.call ++ natWord r.offset ++
    (List.ofFn r.corners).flatMap natWord ++ frame r.witness

/-- `def:mask` and witness (W2), paper/paper.tex: the selected mixed-residual population is taken over both
original gate banks in their complete source occurrence order. -/
def PopulationRequest.value (r : PopulationRequest) : ℕ :=
  StageCert.populationPrefix (r.call.first.gates ++ r.call.second.gates)
    r.corners r.witness r.offset (r.call.first.gates.length + r.call.second.gates.length)

/-- `def:mask`, paper/paper.tex: the population
reply is one exact natural value with the ordinary stream framing. -/
def PopulationRequest.output (r : PopulationRequest) : List Bool := frame (natWord r.value)

end NearQuarticWires.StageMainMask
