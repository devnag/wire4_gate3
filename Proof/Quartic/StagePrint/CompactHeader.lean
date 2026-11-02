import Proof.Quartic.StagePrint.HeaderSource
import Proof.Quartic.StageMain.CompactDecode

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual compact prepared-source reader supplies the same finite call, parameter records and witness bits used by the common affine header, with no recovery index or prime required. -/
theorem HeaderSourceData.of_compact (r : HeaderCall) {a : DS VV MM}
    (h : StageMain.Compact.Decoded r.call r.parameters
      (NearQuarticWires.Program.witnessPrefix r.call r.parameters r.witness) a) :
    HeaderSourceData r a :=⟨h.originalCall,h.scalarFields,h.witnessBits⟩

end NearQuarticWires.StagePrint.Header
