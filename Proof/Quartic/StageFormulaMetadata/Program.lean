import Proof.Quartic.StageFormulaMetadata.EmitPass

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream)

/-- `lem:print`, paper/paper.tex: the single
actual formatter acquires raw input, counts its postfix metadata,
writes the computed header, and rereads/emits its normalized payload. -/
def formatterProgram : St VV MM :=
  .seq acquirePacket (.seq countPacket (.seq buildHeader emitPacket))

/-- `prop:time`, paper/paper.tex: the exact
source clock charges cold acquisition, both complete token passes,
both actual source rewinds and every header operation. -/
def formatterSteps (packet : RawWalkPacket) (tokens : List Tok) (width : ℕ) : ℕ :=
  acquireCost packet+1+((packet.payload.length+9+metadataLoopCost packet.modulus tokens+1)+1+
    (headerSteps packet tokens width+1+
      (packet.payload.length+9+metadataLoopCost packet.modulus tokens+1)))

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed cold program derives the complete unchanged
indexed compiler request from the actual finite raw postfix packet.
Formula validity is an erased source-codec proof, never tape data. -/
theorem formatterProgram_spec (C : Ctx) (packet : RawWalkPacket) (tokens : List Tok)
    (hsource : packet.payload=tokenStream tokens) (hmode : packet.modulus=0 ∨ 2 ≤ packet.modulus)
    (hin : C.inp=packet.word) (hwidth : finiteWidth packet.word.length≤C.Wd) :
    Hs C formatterProgram (a0 : DS VV MM) (formatterSteps packet tokens C.Wd)
      (fun b=>b.out=formattedWord packet.index packet.degree packet.arity packet.modulus tokens) := by
  unfold formatterProgram formatterSteps
  refine (Hs.seq (t2:=(packet.payload.length+9+metadataLoopCost packet.modulus tokens+1)+1+
      (headerSteps packet tokens C.Wd+1+
        (packet.payload.length+9+metadataLoopCost packet.modulus tokens+1)))
    (acquirePacket_spec C packet hin hwidth) fun a ha=>?_).mono (by omega) (fun _ h=>h)
  refine (Hs.seq (t2:=headerSteps packet tokens C.Wd+1+
      (packet.payload.length+9+metadataLoopCost packet.modulus tokens+1))
    (countPacket_spec C packet tokens hsource hmode hwidth a ha) fun b hb=>?_).mono
      (by omega) (fun _ h=>h)
  refine (Hs.seq (t2:=packet.payload.length+9+metadataLoopCost packet.modulus tokens+1)
    (buildHeader_spec C packet tokens hsource hmode hwidth b hb) fun d hd=>?_).mono
      (by omega) (fun _ h=>h)
  exact emitPacket_spec C packet tokens hsource hmode hwidth d hd

end NearQuarticWires.StageFormulaMetadata
