import Proof.Quartic.StageFormulaMetadata.RawBounds

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream)

/-- `prop:time`, paper/paper.tex: every real
postfix counter and field fits the measured finite-source workspace. -/
structure LoopCapacity (packet : RawWalkPacket) (tokens : List Tok) (width : ℕ) : Prop where
  widthBound : 5≤width
  fields : ∀ token∈tokens,tokenFieldWidth token+2≤width
  raw : (tokenStream tokens).length<2^width
  normalized : (tokenStream (normalizeTokens packet.modulus tokens)).length<2^width
  count : tokens.length<2^width
  size : (tokens.map tokenAstSize).sum<2^width
  modulus : 2*packet.modulus≤2^width
  setup : setupValue packet.degree packet.arity (tokens.map tokenAstSize).sum tokens.length
    (tokenStream (normalizeTokens packet.modulus tokens)).length packet.modulus<2^width

/-- `prop:time`, paper/paper.tex: the complete
token-loop capacity contract is derived from the literal source
packet, not supplied by a formula or decoded metadata oracle. -/
theorem raw_loopCapacity (packet : RawWalkPacket) (tokens : List Tok) (width : ℕ)
    (hsource : packet.payload=tokenStream tokens) (hmode : packet.modulus=0 ∨ 2 ≤ packet.modulus)
    (hwidth : finiteWidth packet.word.length≤width) : LoopCapacity packet tokens width := by
  have hW : 5≤width := by unfold finiteWidth at hwidth;omega
  have hL : packet.word.length<2^width :=
    (show packet.word.length<2^packet.word.length from Nat.lt_two_pow_self).trans_le
      (Nat.pow_le_pow_right (by decide) (by unfold finiteWidth at hwidth;omega))
  have hraw : (tokenStream tokens).length≤packet.word.length := by
    rw [←hsource]
    exact rawPayload_length packet
  have hcount:=tokenCount_le_stream tokens
  have hsetup:= (raw_setup_fits packet tokens hsource hmode).trans_le
    (Nat.pow_le_pow_right (by decide) hwidth)
  have hb:=hint_partial_bounds packet.degree packet.arity (tokens.map tokenAstSize).sum tokens.length
    (tokenStream (normalizeTokens packet.modulus tokens)).length packet.modulus
  dsimp only at hb
  have hbase : hintBaseValue packet.arity (tokens.map tokenAstSize).sum tokens.length
      (tokenStream (normalizeTokens packet.modulus tokens)).length packet.modulus<2^width :=
    lt_of_le_of_lt (hb.2.2.2.1.trans hb.2.2.2.2.2.1) hsetup
  refine ⟨hW,?_,hraw.trans_lt hL,?_,hcount.trans_lt (hraw.trans_lt hL),?_,?_,hsetup⟩
  · intro token hmem
    have hfield:=(tokenFieldWidth_le_word token).trans (tokenWord_le_stream tokens token hmem)
    unfold finiteWidth at hwidth
    omega
  · have hformula:=lt_of_le_of_lt hb.2.2.1 hbase
    unfold formulaLengthValue at hformula
    omega
  · unfold hintBaseValue at hbase
    omega
  · have hbits:=rawField_length packet packet.modulus (by simp [RawWalkPacket.header])
    rw [natWord_length] at hbits
    have hmod:=lt_natBitLength packet.modulus
    have hpow : 2^(natBitLength packet.modulus+1)≤2^width :=
      Nat.pow_le_pow_right (by decide) (by unfold finiteWidth at hwidth;omega)
    rw [pow_succ] at hpow
    omega

end NearQuarticWires.StageFormulaMetadata
