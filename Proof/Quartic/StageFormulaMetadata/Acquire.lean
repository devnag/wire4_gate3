import Proof.Quartic.StageFormulaMetadata.RawBounds
import Proof.Quartic.StageFormulaMetadata.HeaderFields
import Proof.Quartic.StageFormulaMetadata.FrameRetain
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open StageRecovery (modulusVar)

/-- `lem:print`, paper/paper.tex: actual cold
packet entry initializes constants, decodes its four scalar fields,
and retains/counts the following original framed postfix bytes. -/
def acquirePacket : St VV MM :=
  .seq initP (.seq readRawHeader (readCountedFrame 0))

/-- `prop:time`, paper/paper.tex: cold source
entry prices its initialization, scalar reads and actual payload bits. -/
def acquireCost (packet : RawWalkPacket) : ℕ := rawHeaderCost packet+10*packet.payload.length+11

/-- `lem:print`, paper/paper.tex: the complete
source state is obtained from the literal raw packet without a decoded
header, length, postfix formula or metadata-count premise. -/
structure Acquired (packet : RawWalkPacket) (a : DS VV MM) : Prop where
  index : a.env rawIndexVar=packet.index
  degree : a.env rawDegreeVar=packet.degree
  modulus : a.env modulusVar=packet.modulus
  arity : a.env rawArityVar=packet.arity
  payloadLength : a.env payloadLengthVar=packet.payload.length
  consumed : a.env consumedVar=0
  tokenCount : a.env countedTokensVar=0
  syntaxCount : a.env syntaxSizeVar=0
  emitted : a.env emittedLengthVar=0
  memory : a.ram 0=packet.payload.map Bool.toNat
  cursor : a.rc 0=packet.payload.length
  input : a.ip=packet.word.length
  output : a.out=[]
  constants : Cst a

/-- `lem:print` and `prop:time`, paper/paper.tex: every acquired register and source record comes from
actual instructions over the finite raw packet, using only workspace
that its measured setup really allocates. -/
theorem acquirePacket_spec (C : Ctx) (packet : RawWalkPacket)
    (hin : C.inp=packet.word) (hwidth : finiteWidth packet.word.length≤C.Wd) :
    Hs C acquirePacket (a0 : DS VV MM) (acquireCost packet) (Acquired packet) := by
  have hW : 5≤C.Wd := by unfold finiteWidth at hwidth;omega
  have hpow : 2<2^C.Wd := by
    have h : 2^2≤2^C.Wd := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at h
    omega
  have hpayload : packet.payload.length<2^C.Wd := by
    have hp:=rawPayload_length packet
    have hlen : packet.word.length<2^C.Wd := by
      have h : packet.word.length<2^packet.word.length := Nat.lt_two_pow_self
      exact h.trans_le (Nat.pow_le_pow_right (by decide) (by unfold finiteWidth at hwidth;omega))
    omega
  unfold acquirePacket
  refine (Hs.seq (t2:=rawHeaderCost packet+10*packet.payload.length+5)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl hpow)
    fun a ⟨hc,hram,hrc,hip,hout,_hkin,_hkout,_hkc,hfr⟩=>?_).mono
      (by unfold acquireCost;omega) (fun _ h=>h)
  have hhead : C.inp.drop a.ip=packet.header.flatMap natWord++frame packet.payload := by
    rw [hip,hin]
    simpa only [a0,List.drop_zero] using packet.word_header
  have hfields : ∀ value∈packet.header,natBitLength value+2≤C.Wd := by
    intro value hv
    have h:=rawField_length packet value hv
    rw [natWord_length] at h
    unfold finiteWidth at hwidth
    omega
  refine (Hs.seq (t2:=10*packet.payload.length+4)
    (readRawHeader_spec C packet (frame packet.payload) a hc hhead hfields)
    fun b ⟨hbindex,hbdegree,hbmod,hbarity,hbip,hbrest,hbc,hbf⟩=>?_).mono
      (by omega) (fun _ h=>h)
  simp only [Prod.mk.injEq] at hbrest
  rcases hbrest with ⟨hbout,hbram,hbrc,_hbkin,_hbkout,_hbkc⟩
  have hbpayload : b.env payloadLengthVar=0 := by
    rw [hbf _ (by decide),hfr _ (by decide)]
    rfl
  have hbsource : C.inp.drop b.ip=frame packet.payload++[] := by
    rw [hbip,hip,hin]
    change packet.word.drop (0+(packet.header.flatMap natWord).length)=_
    rw [Nat.zero_add,packet.word_header,List.drop_left,List.append_nil]
  have hbzero : b.ram 0=[] ∧ b.rc 0=0 := by rw [hbram,hbrc,hram,hrc];exact ⟨rfl,rfl⟩
  refine (readCountedFrame_spec C 0 packet.payload [] b hbc hbsource
    (by rw [hbzero.1,hbzero.2];rfl) (by rw [hbpayload];simpa using hpayload)).mono le_rfl ?_
  rintro last ⟨hlpayload,hlip,hlram,hlrc,_hlother,hlrest,hlc,hlf⟩
  refine ⟨by rw [hlf _ (by decide),hbindex],by rw [hlf _ (by decide),hbdegree],
    by rw [hlf _ (by decide),hbmod],by rw [hlf _ (by decide),hbarity],
    by simpa only [hbpayload,Nat.zero_add] using hlpayload,?_,?_,?_,?_,?_,?_,?_,?_,hlc⟩
  · rw [hlf _ (by decide),hbf _ (by decide),hfr _ (by decide)];rfl
  · rw [hlf _ (by decide),hbf _ (by decide),hfr _ (by decide)];rfl
  · rw [hlf _ (by decide),hbf _ (by decide),hfr _ (by decide)];rfl
  · rw [hlf _ (by decide),hbf _ (by decide),hfr _ (by decide)];rfl
  · simpa only [hbzero.1,List.nil_append] using hlram
  · simpa only [hbzero.2,Nat.zero_add] using hlrc
  · rw [hlip,hbip,hip,packet.word_header,List.length_append]
    simp only [a0,Nat.zero_add]
  · have hlo : last.out=b.out := congrArg Prod.fst hlrest
    rw [hlo,hbout,hout]
    rfl

end NearQuarticWires.StageFormulaMetadata
