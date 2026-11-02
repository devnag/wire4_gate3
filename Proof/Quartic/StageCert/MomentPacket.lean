import Proof.Quartic.StageCert.MomentPayload
import Proof.Quartic.StageCert.MomentSourceBounds
import Proof.Quartic.StageLift.OutputPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats
open StageLift StageRecovery

/-- `lem:print`, paper/paper.tex: the exact raw
packet has four actual natural header fields followed by its framed
original signed Formula tokens. Only the payload is marked. -/
def emitMomentPacket : St VV MM :=
  .seq prepareMomentHeader (.seq emitRawWalkHeader (OutputFrame.framedProgram emitMomentPayload))

/-- `prop:time`, paper/paper.tex: header
serialization and exact payload framing add their literal bit clocks
to the complete original signed moment source. -/
noncomputable def MomentRequest.packetSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*(40*(32*r.bodyScale+10)+43)+3*r.payloadSteps+700

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual source records and actual flag suffix
produce exactly the q=0 packet, retaining all signed bad-column values. -/
theorem emitMomentPacket_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a) (hd : MomentSourceData r a)
    (hwidth : r.bodyCapacity≤C.Wd)
    (hRC : ∀m,a.rc m≤(a.ram m).length) (hKC : a.kc≤a.kout.length)
    (hin : C.inp.drop a.ip=structuralFlagList r (momentFlagEdges r.test)++rest) :
    Hs C emitMomentPacket a r.packetSteps (fun z=>
      z.out=a.out++r.packet.word ∧ z.ip=a.ip+(momentFlagEdges r.test).length ∧ Cst z) := by
  have hcap := r.body_capacity C.Wd hwidth
  let S := r.bodyScale
  let B := 32*S+10
  have hS : 2≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hlinear : 100*S≤C.Wd := by
    change 100*S^2≤C.Wd at hwidth
    nlinarith
  have hBit : B+2<2^C.Wd := by
    have hp := Nat.lt_two_pow_self (n := C.Wd)
    dsimp only [B]
    omega
  have hword : r.word.length≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hG : (Builder.allGates r.call).length≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hX : r.selected.1.Xmax≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hk : r.selected.1.k≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hnbl (v : ℕ) : natBitLength v≤v+1 := by
    unfold natBitLength
    have hh := Nat.log_le_self 2 v
    omega
  unfold emitMomentPacket
  apply Hx.hs
  refine Hs.then ((prepareMomentHeader_run C r.call r.rules a hc hd.parameters
    (by have hh := hcap.minWidth; omega) hcap.degree hcap.atoms).rc_le hRC hKC)
    (fun b ⟨⟨bd,bv,bq,bG,bG1,br,bs,bc,bf⟩,bRC,bKC⟩ n1 hn1=>?_)
  have bip : b.ip=a.ip := congrArg (fun q=>q.1) bs
  have bout : b.out=a.out := congrArg (fun q=>q.2.1) bs
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  have bindex : b.env printWalkIndex=r.index.val :=
    (bf _ (by decide)).trans (hd.fields ⟨5,by decide⟩)
  have hheader : ∀x∈rawHeaderFields,natBitLength (b.env x)≤B := by
    intro x hx
    rcases (by simpa only [rawHeaderFields,List.mem_cons,List.not_mem_nil,or_false] using hx) with
      rfl|rfl|rfl|rfl
    · rw [bindex]
      have hh := r.value_bits r.index.val (by simp [MomentRequest.sourceValues])
      dsimp only [B]
      omega
    · rw [bd]
      have hh := hnbl (16*r.selected.1.Xmax+8*r.selected.1.k)
      dsimp only [B]
      omega
    · rw [bq]
      have hh : natBitLength 0=1 := rfl
      rw [hh]
      dsimp only [B]
      omega
    · rw [bv]
      have hh := hnbl (17*(Builder.allGates r.call).length)
      dsimp only [B]
      omega
  refine Hs.then ((emitRawWalkHeader_spec C b bc B hheader
    (by have hh := hcap.minWidth; omega) hBit).rc_le bRC bKC)
    (fun c ⟨⟨co,cs,cc,cf⟩,cRC,cKC⟩ n2 hn2=>?_)
  have cip : c.ip=b.ip := congrArg (fun q=>q.1) cs
  have cram : c.ram=a.ram := (congrArg (fun q=>q.2.1) cs).trans bram
  have cfields (i : Fin 6) : c.env momentSourceFields[i]=r.sourceValues[i] :=
    (cf _ (by fin_cases i <;> decide)).trans
      ((bf _ (by fin_cases i <;> decide)).trans (hd.fields i))
  let c0 : DS VV MM := {c with out:=[]}
  have cp := emitMomentPayload_run C r rest c0 ⟨cc.z,cc.one,cc.two⟩ hcap
    (by change c.ram parameterStore=_; rw [cram]; exact hd.parameters)
    (by change c.ram witnessStore=_; rw [cram]; exact hd.witness)
    (by change c.ram factorStore=_; rw [cram]; exact hd.factors)
    cfields ((cf _ (by decide)).trans bG) ((cf _ (by decide)).trans bG1) cRC cKC
    (by change C.inp.drop c.ip=_; rw [cip,bip]; exact hin)
  obtain ⟨d,n,he,hn,doo,di,_,dc⟩ := cp
  have hf := framedProgram_afterPrefix he rfl c.out
  have hdo : d.out=(toks r.formula).flatMap tokWord := by
    simpa only [c0,List.nil_append] using doo
  refine ⟨{d with out:=c.out++frame d.out},3*n+2,?_,⟨?_,?_,⟨dc.z,dc.one,dc.two⟩⟩,?_⟩
  · simpa only [c0] using hf
  · change c.out++frame d.out=a.out++r.packet.word
    rw [co,bout,bindex,bd,bq,bv,hdo]
    simp only [MomentRequest.packet,StageFormulaMetadata.RawWalkPacket.word,List.append_assoc]
  · change d.ip=_
    rw [di,cip,bip]
  · rw [hd.parameterCursor] at hn1
    change n2≤4*(40*B+43)+1 at hn2
    unfold MomentRequest.packetSteps
    dsimp only [B,S] at hn2 ⊢
    omega

end NearQuarticWires.StageCert.Tokens
