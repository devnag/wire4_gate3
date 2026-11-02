import Proof.Quartic.StageFormulaMetadata.Program
import Proof.Quartic.StageFormulaMetadata.OutputBounds

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream)

/-- `prop:time`, paper/paper.tex: the entire
actual two-pass formatter has an explicit quadratic source clock in
the literal raw packet bits, even when syntax exponents are large. -/
theorem formatterSteps_le (packet : RawWalkPacket) (tokens : List Tok)
    (hsource : packet.payload=tokenStream tokens) (hmode : packet.modulus=0 ∨ 2 ≤ packet.modulus) :
    formatterSteps packet tokens (finiteWidth packet.word.length)≤1000000*(packet.word.length+1)^2 := by
  let len:=packet.word.length
  have hraw : (tokenStream tokens).length≤len := by rw [←hsource];exact rawPayload_length packet
  have hcount : tokens.length≤len := (tokenCount_le_stream tokens).trans hraw
  have hbits (value : ℕ) (hv : value∈packet.header) : natBitLength value≤len := by
    have h:=rawField_length packet value hv
    rw [natWord_length] at h
    omega
  have hq : natBitLength packet.modulus≤len := hbits _ (by simp [RawWalkPacket.header])
  have ha : natBitLength packet.arity≤len := hbits _ (by simp [RawWalkPacket.header])
  have hn : natBitLength tokens.length≤len+1 := by
    have h:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self tokens.length
    omega
  have hsum : (packet.header.map natBitLength).sum≤4*len := by
    have h:=List.sum_le_card_nsmul (packet.header.map natBitLength) len (by
      intro value hv
      obtain ⟨field,hfield,rfl⟩:=List.mem_map.mp hv
      exact hbits field hfield)
    simpa only [List.length_map,RawWalkPacket.header,List.length_cons,List.length_nil,smul_eq_mul] using h
  have hpayload : packet.payload.length≤len := rawPayload_length packet
  have hacquire : acquireCost packet≤130*len+142 := by
    unfold acquireCost rawHeaderCost
    omega
  have hheader : headerSteps packet tokens (finiteWidth packet.word.length)≤32015*len+32471 := by
    unfold headerSteps finiteWidth
    dsimp only [len] at ha hq hn ⊢
    omega
  have hloop : metadataLoopCost packet.modulus tokens≤1002*(len+len*(len+1))+2 := by
    have h:=metadataLoopCost_le packet.modulus tokens hmode
    have hp:=Nat.mul_le_mul hcount (show natBitLength packet.modulus+1≤len+1 by omega)
    omega
  unfold formatterSteps
  dsimp only [len] at hacquire hheader hloop hpayload ⊢
  nlinarith

end NearQuarticWires.StageFormulaMetadata
