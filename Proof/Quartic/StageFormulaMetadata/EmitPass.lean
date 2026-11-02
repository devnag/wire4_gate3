import Proof.Quartic.StageFormulaMetadata.HeaderPass

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream modulusVar)

/-- `lem:print`, paper/paper.tex: the actual
eight scalar fields followed by the normalized payload are exactly
the unchanged indexed compiler request in the frozen ABI. -/
theorem header_append_payload (packet : RawWalkPacket) (tokens : List Tok) :
    packetFormattedHeader packet tokens++tokenStream (normalizeTokens packet.modulus tokens)=
      formattedWord packet.index packet.degree packet.arity packet.modulus tokens := by
  have hh : hintValue packet.arity (tokens.map tokenAstSize).sum tokens.length
      (tokenStream (normalizeTokens packet.modulus tokens)).length packet.modulus=
        countedHint packet.arity packet.modulus tokens := hintValue_eq packet.arity packet.modulus tokens
  simp only [packetFormattedHeader,setupValue,hh,formattedWord,countedFormulaWord,normalizedPayload,
    List.append_assoc]

/-- `lem:print`, paper/paper.tex: the final
pass rereads the actual retained raw payload after its paid rewind. -/
def emitPacket : St VV MM := .seq resetPass (metadataLoop true)

/-- `lem:print` and `prop:time`, paper/paper.tex: the second physical token pass appends every actual
normalized token after the computed header, including exact signed
constants at modulus zero, without a supplied output word. -/
theorem emitPacket_spec (C : Ctx) (packet : RawWalkPacket) (tokens : List Tok)
    (hsource : packet.payload=tokenStream tokens) (hmode : packet.modulus=0 ∨ 2 ≤ packet.modulus)
    (hwidth : finiteWidth packet.word.length≤C.Wd) (a : DS VV MM) (ha : HeaderReady packet tokens a) :
    Hs C emitPacket a (packet.payload.length+9+metadataLoopCost packet.modulus tokens+1)
      (fun b=>b.out=formattedWord packet.index packet.degree packet.arity packet.modulus tokens) := by
  have cap:=raw_loopCapacity packet tokens C.Wd hsource hmode hwidth
  have eReset:=resetPass_spec C a ha.constants
  rw [ha.cursor] at eReset
  unfold emitPacket
  refine Hs.seq (t2:=metadataLoopCost packet.modulus tokens) eReset
    fun b ⟨hbcons,hbcount,hbsize,hboutlen,hbrc,hbram,_hbother,hbrest,hbc,hbf⟩=>?_
  have hbq : b.env modulusVar=packet.modulus := by rw [hbf _ (by decide),ha.modulus]
  have hbmem : b.ram 0=packet.payload.map Bool.toNat := by rw [hbram,ha.memory]
  have hblimit : b.env payloadLengthVar=b.env consumedVar+(tokenStream tokens).length := by
    rw [hbf _ (by decide),ha.payloadLength,hbcons,hsource,Nat.zero_add]
  have hinput : packet.payload.drop (b.rc 0)=tokenStream tokens++[] := by rw [hbrc,hsource];simp
  refine (metadataLoop_spec C true tokens b hbc packet.payload hbmem [] hinput packet.modulus hbq hmode
    cap.modulus cap.widthBound cap.fields hblimit (by rw [hbcons,Nat.zero_add];exact cap.raw)
    (by rw [hboutlen,Nat.zero_add];exact cap.normalized) (by rw [hbcount,Nat.zero_add];exact cap.count)
    (by rw [hbsize,Nat.zero_add];exact cap.size)).mono le_rfl ?_
  intro last hl
  have hbout : b.out=a.out := congrArg (fun r=>r.2.1) hbrest
  rw [hl.output,hbout,ha.output]
  exact header_append_payload packet tokens

end NearQuarticWires.StageFormulaMetadata
