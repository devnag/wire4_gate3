import Proof.Gates.Interfaces.Counter

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)

/-- `lem:print`, paper/paper.tex:
one actual per-walk postfix word carries only its original index,
degree, modulus, atom arity and physically emitted raw token bytes. -/
structure RawWalkPacket where
  index : ℕ
  degree : ℕ
  modulus : ℕ
  arity : ℕ
  payload : List Bool

/-- `lem:print`, paper/paper.tex:
the four scalar fields precede the actual framed postfix payload;
no token count, byte count, syntax size or workspace hint is supplied. -/
def RawWalkPacket.word (packet : RawWalkPacket) : List Bool :=
  natWord packet.index ++ natWord packet.degree ++ natWord packet.modulus ++
    natWord packet.arity ++ frame packet.payload

/-- `lem:print`, paper/paper.tex:
the exact raw scalar header preserves its original field order. -/
def RawWalkPacket.header (packet : RawWalkPacket) : List ℕ :=
  [packet.index,packet.degree,packet.modulus,packet.arity]

/-- `lem:print`, paper/paper.tex:
the intermediate request uses the existing natural and Boolean
frame codecs with no additional formula representation. -/
theorem RawWalkPacket.word_header (packet : RawWalkPacket) :
    packet.word = packet.header.flatMap natWord ++ frame packet.payload := by
  simp [RawWalkPacket.word,RawWalkPacket.header,List.append_assoc]

end NearQuarticWires.StageFormulaMetadata
