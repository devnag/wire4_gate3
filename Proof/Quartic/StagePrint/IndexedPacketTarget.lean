import Proof.Quartic.StagePrint.DownstreamTargets
import Proof.Quartic.StageRecovery.FamilySource

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Downstream

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- `lem:print`, paper/paper.tex: the actual
modular formatter retains one encoded walk index before the unchanged
finite-family compiler request. -/
structure IndexedFamilyPacket where
  index : ℕ
  request : StageRecovery.FamilyCompileRequest

def IndexedFamilyPacket.word (r : IndexedFamilyPacket) : List Bool :=
  natWord r.index++r.request.word

/-- `lem:print` and `prop:time`, paper/paper.tex: a cold finite-packet adapter removes only the
encoded index, preserving the actual compiler bytes and every constant. -/
abbrev ModularPacketProjection :=
  WordFunction IndexedFamilyPacket IndexedFamilyPacket.word (fun r=>frame r.request.word)
    (fun r=>10^8*(r.word.length+1)^2)

#check ModularPacketProjection

end NearQuarticWires.StagePrint.Downstream
