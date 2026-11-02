import Proof.Quartic.StageCompiledTerms.CarrierCodec
import Proof.Quartic.StageCompiledTerms.PacketCompiler
import Proof.Quartic.Reconstruct.BatchLoopRun

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord)
open NearCubicGates.Close.Interfaces.Formats
open NearQuarticWires.Reconstruct.Batch

/-- Step 3, `sec:algorithm`, paper/paper.tex: every original
low-first walk is retained, including its zero Gamma case. -/
noncomputable def walkRequests {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List (WalkRequest B1 B2) :=
  List.ofFn fun index=>⟨r,index⟩

/-- `lem:print`, paper/paper.tex: each batch
input is the actual literal five-field source packet. -/
noncomputable def walkInput {B1 B2 : ℕ} (w : WalkRequest B1 B2) : List Bool :=
  (StageLift.sourceWalkPacket w.1 w.2).word

/-- `lem:print`, paper/paper.tex: each reply is
the actual compiler's framed canonical Terms word. -/
noncomputable def walkAnswer {B1 B2 : ℕ} (w : WalkRequest B1 B2) : List Bool :=
  frame (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2))

/-- `lem:print`, paper/paper.tex: the original
encoded index, selected degree and actual modulus form the paid tag. -/
noncomputable def walkTag {B1 B2 : ℕ} (w : WalkRequest B1 B2) : List Bool :=
  packetTag (StageLift.sourceWalkPacket w.1 w.2)

/-- Step 3, `sec:algorithm`, paper/paper.tex: the original
preparation length and bytes occupy the batch's sole context copy. -/
noncomputable def batchContext {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  natWord (StageLift.preparedWordOf r).length++StageLift.preparedWordOf r

/-- `lem:print`, paper/paper.tex: measured
packet isolation produces the exact ordinary batch input codec. -/
theorem actual_batch_input {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualCarrier r).batchWord=frame (batchContext r)++
      listWord (fun w=>frame (walkTag w)++frame (walkInput w)) (walkRequests r) := by
  simp only [actualCarrier,RawCarrier.batchWord,taggedPacketWords,batchContext,
    listWord,walkRequests,List.length_ofFn,List.flatMap_def,List.map_ofFn,walkTag,walkInput,List.append_assoc]
  rfl

/-- `lem:print`, paper/paper.tex: the copied
tag and literal compiler reply are exactly the frozen entry bytes. -/
theorem walk_entry {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    walkTag w++walkAnswer w=StagePrint.TermsCarrier.entryWord w.1 w.2 := by
  simp only [walkTag,packetTag,walkAnswer,StageLift.sourceWalkPacket,
    StagePrint.TermsCarrier.entryWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

/-- Step 3 and `lem:print`, paper/paper.tex: the actual batch result preserves the exact original
one-copy carrier, walk order, degree, modulus and compiled Terms. -/
theorem actual_batch_output {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    batchOut (batchContext r) walkTag walkAnswer (walkRequests r)=StagePrint.TermsCarrier.word r := by
  simp only [batchOut,listWord,walkRequests,List.length_ofFn,walk_entry,
    List.flatMap_def,List.map_ofFn,StagePrint.TermsCarrier.word,batchContext,List.append_assoc]
  rfl

end NearQuarticWires.StageCompiledTerms
