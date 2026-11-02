import Proof.Quartic.StageFormulaMetadata.OutputBounds
import Proof.Quartic.StageFormulaMetadata.HintValues
import Proof.Quartic.StageFormulaMetadata.FiniteSetup

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream)

/-- `prop:time`, paper/paper.tex: every decoded
raw scalar is bounded by its physically present source field. -/
theorem rawField_length (packet : RawWalkPacket) (value : ℕ) (hmem : value∈packet.header) :
    (natWord value).length≤packet.word.length := by
  simp only [RawWalkPacket.header,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  all_goals simp only [RawWalkPacket.word,List.length_append]
  all_goals omega

/-- `prop:time`, paper/paper.tex: raw payload
bytes are bounded by the complete finite packet scanned at setup. -/
theorem rawPayload_length (packet : RawWalkPacket) : packet.payload.length≤packet.word.length := by
  simp only [RawWalkPacket.word,List.length_append,frame_length]
  omega

/-- `prop:time`, paper/paper.tex: raw scalar
values fit within the actual finite packet's binary length. -/
theorem rawField_value (packet : RawWalkPacket) (value : ℕ) (hmem : value∈packet.header) :
    value<2^packet.word.length := by
  have hlength:=rawField_length packet value hmem
  rw [natWord_length] at hlength
  exact (lt_natBitLength value).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- `prop:time`, paper/paper.tex: all syntax
and compiler hints fit the workspace actually initialized by scanning
the raw packet, including binary powers and signed normalization. -/
theorem raw_setup_fits (packet : RawWalkPacket) (tokens : List Tok)
    (hsource : packet.payload=tokenStream tokens) (hmode : packet.modulus=0 ∨ 2 ≤ packet.modulus) :
    setupValue packet.degree packet.arity (tokens.map tokenAstSize).sum tokens.length
      (tokenStream (normalizeTokens packet.modulus tokens)).length packet.modulus<
        2^finiteWidth packet.word.length := by
  let len:=packet.word.length
  let radix:=2^(len+1)
  have hradix : 2≤radix := by
    dsimp [radix]
    exact (by norm_num : 2^1=2) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hlen : len+1≤radix := by
    have h:=Nat.lt_two_pow_self (n:=len+1)
    dsimp [radix]
    omega
  have hraw : (tokenStream tokens).length≤len := by rw [←hsource];exact rawPayload_length packet
  have hcount : tokens.length≤len := (tokenCount_le_stream tokens).trans hraw
  have hq : natBitLength packet.modulus≤len := by
    have h:=rawField_length packet packet.modulus (by simp [RawWalkPacket.header])
    rw [natWord_length] at h
    omega
  have harityword : (natWord packet.arity).length≤len :=
    rawField_length packet packet.arity (by simp [RawWalkPacket.header])
  have hA : packet.arity≤radix := by
    have h:=rawField_value packet packet.arity (by simp [RawWalkPacket.header])
    change packet.arity<2^len at h
    have hp : 2^len≤radix := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hD : packet.degree≤radix := by
    have h:=rawField_value packet packet.degree (by simp [RawWalkPacket.header])
    change packet.degree<2^len at h
    have hp : 2^len≤radix := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hSyntax : (tokens.map tokenAstSize).sum≤radix^2 := by
    have h:=syntaxSum_le_stream tokens
    have hp : 2^(tokenStream tokens).length≤radix := Nat.pow_le_pow_right (by decide) (by omega)
    have hm:=Nat.mul_le_mul (show tokens.length≤radix by omega) hp
    nlinarith
  have hOut : (tokenStream (normalizeTokens packet.modulus tokens)).length≤3*radix^2 := by
    have h:=normalizedStream_length_le packet.modulus tokens hmode
    have hprod:=Nat.mul_le_mul (show tokens.length≤radix by omega)
      (show 2*natBitLength packet.modulus≤2*radix by omega)
    nlinarith
  have hNbits : natBitLength tokens.length≤radix := by
    have h:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self tokens.length
    omega
  have hNword : (natWord tokens.length).length≤3*radix^2 := by rw [natWord_length];nlinarith
  have hFormula : formulaLengthValue packet.arity tokens.length
      (tokenStream (normalizeTokens packet.modulus tokens)).length≤7*radix^2 := by
    unfold formulaLengthValue
    nlinarith
  have hBase : hintBaseValue packet.arity (tokens.map tokenAstSize).sum tokens.length
      (tokenStream (normalizeTokens packet.modulus tokens)).length packet.modulus≤20*radix^2 := by
    unfold hintBaseValue
    nlinarith
  have hOuter : packet.degree+packet.arity+10≤12*radix^2 := by nlinarith
  have hBaseSq:=Nat.pow_le_pow_left hBase 2
  have hOuterSq:=Nat.pow_le_pow_left hOuter 2
  have hSetup : setupValue packet.degree packet.arity (tokens.map tokenAstSize).sum tokens.length
      (tokenStream (normalizeTokens packet.modulus tokens)).length packet.modulus≤1024*radix^4 := by
    unfold setupValue hintValue
    nlinarith
  calc _≤1024*radix^4:=hSetup
    _=2^(4*(len+1)+10):=by
      dsimp [radix]
      conv_rhs=>rw [show 4*(len+1)+10=10+(len+1)*4 by omega,pow_add,pow_mul]
      norm_num
    _<2^finiteWidth packet.word.length:=Nat.pow_lt_pow_right (by decide) (by
      unfold finiteWidth
      dsimp [len]
      omega)

end NearQuarticWires.StageFormulaMetadata
