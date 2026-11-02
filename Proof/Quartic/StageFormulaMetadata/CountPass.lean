import Proof.Quartic.StageFormulaMetadata.Acquire
import Proof.Quartic.StageFormulaMetadata.ResetPass
import Proof.Quartic.StageFormulaMetadata.LoopCapacity

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream modulusVar)

/-- `lem:print`, paper/paper.tex: the first
actual token pass computes all metadata before emitting any header. -/
def countPacket : St VV MM := .seq resetPass (metadataLoop false)

/-- `lem:print`, paper/paper.tex: all counted
metadata remains tied to the actual original retained payload. -/
structure Counted (packet : RawWalkPacket) (tokens : List Tok) (a : DS VV MM) : Prop where
  index : a.env rawIndexVar=packet.index
  degree : a.env rawDegreeVar=packet.degree
  modulus : a.env modulusVar=packet.modulus
  arity : a.env rawArityVar=packet.arity
  payloadLength : a.env payloadLengthVar=packet.payload.length
  consumed : a.env consumedVar=packet.payload.length
  tokenCount : a.env countedTokensVar=tokens.length
  syntaxCount : a.env syntaxSizeVar=(tokens.map tokenAstSize).sum
  emitted : a.env emittedLengthVar=(tokenStream (normalizeTokens packet.modulus tokens)).length
  memory : a.ram 0=packet.payload.map Bool.toNat
  cursor : a.rc 0=packet.payload.length
  input : a.ip=packet.word.length
  output : a.out=[]
  constants : Cst a

/-- `lem:print` and `prop:time`, paper/paper.tex: the paid source rewind and complete first pass derive
N, S and normalized L physically from the original raw packet. -/
theorem countPacket_spec (C : Ctx) (packet : RawWalkPacket) (tokens : List Tok)
    (hsource : packet.payload=tokenStream tokens) (hmode : packet.modulus=0 ∨ 2 ≤ packet.modulus)
    (hwidth : finiteWidth packet.word.length≤C.Wd) (a : DS VV MM) (ha : Acquired packet a) :
    Hs C countPacket a (packet.payload.length+9+metadataLoopCost packet.modulus tokens+1)
      (Counted packet tokens) := by
  have cap:=raw_loopCapacity packet tokens C.Wd hsource hmode hwidth
  have eReset:=resetPass_spec C a ha.constants
  rw [ha.cursor] at eReset
  unfold countPacket
  refine Hs.seq (t2:=metadataLoopCost packet.modulus tokens) eReset
    fun b ⟨hbcons,hbcount,hbsize,hboutlen,hbrc,hbram,_hbother,hbrest,hbc,hbf⟩=>?_
  have hbq : b.env modulusVar=packet.modulus := by rw [hbf _ (by decide),ha.modulus]
  have hbmem : b.ram 0=packet.payload.map Bool.toNat := by rw [hbram,ha.memory]
  have hblimit : b.env payloadLengthVar=b.env consumedVar+(tokenStream tokens).length := by
    rw [hbf _ (by decide),ha.payloadLength,hbcons,hsource,Nat.zero_add]
  have hinput : packet.payload.drop (b.rc 0)=tokenStream tokens++[] := by rw [hbrc,hsource];simp
  refine (metadataLoop_spec C false tokens b hbc packet.payload hbmem [] hinput packet.modulus hbq hmode
    cap.modulus cap.widthBound cap.fields hblimit (by rw [hbcons,Nat.zero_add];exact cap.raw)
    (by rw [hboutlen,Nat.zero_add];exact cap.normalized) (by rw [hbcount,Nat.zero_add];exact cap.count)
    (by rw [hbsize,Nat.zero_add];exact cap.size)).mono le_rfl ?_
  intro last hl
  simp only [Prod.mk.injEq] at hbrest
  rcases hbrest with ⟨hbip,hbout,_hbkin,_hbkout,_hbkc⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hl.input.trans (hbip.trans ha.input),?_,hl.constants⟩
  · rw [hl.registers _ (by decide),hbf _ (by decide),ha.index]
  · rw [hl.registers _ (by decide),hbf _ (by decide),ha.degree]
  · rw [hl.registers _ (by decide),hbq]
  · rw [hl.registers _ (by decide),hbf _ (by decide),ha.arity]
  · rw [hl.registers _ (by decide),hbf _ (by decide),ha.payloadLength]
  · rw [hl.consumed,hbcons,Nat.zero_add,←hsource]
  · rw [hl.tokenCount,hbcount,Nat.zero_add]
  · rw [hl.syntaxCount,hbsize,Nat.zero_add]
  · rw [hl.emitted,hboutlen,Nat.zero_add]
  · rw [hl.memory,hbmem]
  · rw [hl.cursor,hbrc,Nat.zero_add,←hsource]
  · rw [hl.output,hbout,ha.output]
    rfl

end NearQuarticWires.StageFormulaMetadata
