import Proof.Quartic.StageCompiledTerms.PacketLoop
import Proof.Quartic.StagePrint.TermsCarrierTarget

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- Step 3 and `lem:print`, paper/paper.tex: the internal correctness index specifies exactly the
actual one-copy source bytes, without adding fields to their tape. -/
structure RawCarrier where
  preparation : List Bool
  packets : List StageFormulaMetadata.RawWalkPacket

/-- Step 3, `sec:algorithm`, paper/paper.tex: one original
preparation and its actual packet census precede the raw packet stream. -/
def RawCarrier.word (r : RawCarrier) : List Bool :=
  natWord r.preparation.length++r.preparation++natWord r.packets.length++
    r.packets.flatMap StageFormulaMetadata.RawWalkPacket.word

/-- `lem:print`, paper/paper.tex: the ordinary
batch receives one framed preparation context and encoded tagged
requests; each packet is framed only by the actual isolation pass. -/
def RawCarrier.batchWord (r : RawCarrier) : List Bool :=
  frame (natWord r.preparation.length++r.preparation)++natWord r.packets.length++
    taggedPacketWords r.packets

/-- Step 3, `sec:algorithm`, paper/paper.tex: the real complete
source supplies this internal correctness index, including every zero
Gamma walk in original low-first order. -/
noncomputable def actualCarrier {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : RawCarrier :=
  ⟨StageLift.preparedWordOf r,List.ofFn (StageLift.sourceWalkPacket r)⟩

/-- Step 3 and `lem:print`, paper/paper.tex: the internal carrier's source word is exactly the
literal output of the sealed original-input producer. -/
theorem actualCarrier_word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualCarrier r).word=StageLift.sourceCarrierWord r := by
  have ht : (List.ofFn (StageLift.sourceWalkPacket r)).take (r.child.cellCall.seed.N^8)=
      List.ofFn (StageLift.sourceWalkPacket r) := List.take_of_length_le (by simp)
  simp only [actualCarrier,RawCarrier.word,List.length_ofFn,StageLift.sourceCarrierWord,
    StageLift.sourcePacketPrefix,ht]

end NearQuarticWires.StageCompiledTerms
