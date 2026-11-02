import Proof.Quartic.StageNativeKidsTail.Request
import Proof.Gates.Cells.OutLen

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open StageNativeKids StageResize

/-- `prop:time`, paper/paper.tex: the actual
raw output's encoded size is paid by the concrete ordinary resize
computation, even when the original inner rows are empty. -/
theorem output_length_le (r : ResizeTailRequest) : r.stream.output.length≤r.stream.budget+1 :=
  NearCubicGates.Close.Cells.wf_out_len streamResizeWordFunction r.stream

end NearQuarticWires.StageNativeKidsTail
