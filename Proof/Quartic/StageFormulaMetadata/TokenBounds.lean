import Proof.Quartic.StageFormulaMetadata.TokenLoop
import Proof.Gates.Cells.InputLen

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream signedNaturalResidue)

/-- `prop:time`, paper/paper.tex: coefficient
normalization needs at most the original or modulus binary width. -/
theorem normalizedMagnitude_bits (modulus magnitude : ℕ) (negative : Bool)
    (hmode : modulus=0 ∨ 2 ≤ modulus) :
    natBitLength (normalizedMagnitude modulus magnitude negative)≤
      natBitLength magnitude+natBitLength modulus := by
  rcases hmode with hzero | hpositive
  · subst modulus
    simp only [normalizedMagnitude,if_true]
    omega
  · have hnz : modulus≠0 := by omega
    have hres : normalizedMagnitude modulus magnitude negative < modulus := by
      unfold normalizedMagnitude
      rw [if_neg hnz]
      cases negative <;> simp only [signedNaturalResidue,Bool.false_eq_true,if_false,if_true]
      all_goals exact Nat.mod_lt _ (by omega)
    have hbits:=nbl_le_of_lt (hres.trans (lt_natBitLength modulus))
      (natBitLength_pos modulus)
    omega

/-- `prop:time`, paper/paper.tex: the source
field width is bounded by its actual encoded token byte length. -/
theorem tokenFieldWidth_le_word (token : Tok) : tokenFieldWidth token≤(tokWord token).length := by
  cases token <;> simp only [tokenFieldWidth,tokWord,integerWord_fields,List.length_append,
    natWord_length] <;> omega

/-- `prop:time`, paper/paper.tex: each unary
syntax contribution fits an exponential in its real binary codec. -/
theorem tokenAstSize_le_pow_word (token : Tok) :
    tokenAstSize token≤2^(tokWord token).length := by
  cases token with
  | pow exponent =>
      have hbits:=lt_natBitLength exponent
      have hlength : natBitLength exponent≤(tokWord (Tok.pow exponent)).length :=
        tokenFieldWidth_le_word (Tok.pow exponent)
      have hpow:=Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hlength
      change exponent+1≤_
      omega
  | const _ | var _ | add | neg | sub | mul => exact Nat.one_le_two_pow

/-- `prop:time`, paper/paper.tex: one member's
literal codec is bounded by the actual complete postfix payload. -/
theorem tokenWord_le_stream (tokens : List Tok) (token : Tok) (hmem : token∈tokens) :
    (tokWord token).length≤(tokenStream tokens).length := by
  induction tokens with
  | nil => simp at hmem
  | cons first tokens ih =>
      simp only [List.mem_cons] at hmem
      simp only [tokenStream,List.flatMap_cons,List.length_append]
      rcases hmem with rfl | hmem
      · omega
      · have htail:=ih hmem
        simp only [tokenStream] at htail
        omega

/-- `prop:time`, paper/paper.tex: the actual
postfix token count is bounded by the physically scanned payload. -/
theorem tokenCount_le_stream (tokens : List Tok) : tokens.length≤(tokenStream tokens).length := by
  induction tokens with
  | nil => simp [tokenStream]
  | cons token tokens ih =>
      have hp:=tokenWord_pos token
      simp only [tokenStream] at ih
      simp only [List.length_cons,tokenStream,List.flatMap_cons,List.length_append]
      omega

/-- `prop:time`, paper/paper.tex: even binary
power exponents keep the entire syntax counter within a register
whose width is linear in the actual postfix payload length. -/
theorem syntaxSum_le_stream (tokens : List Tok) :
    (tokens.map tokenAstSize).sum≤tokens.length*2^(tokenStream tokens).length := by
  have hsum:=List.sum_le_card_nsmul (tokens.map tokenAstSize) (2^(tokenStream tokens).length) (by
    intro value hv
    obtain ⟨token,hmem,rfl⟩:=List.mem_map.mp hv
    exact (tokenAstSize_le_pow_word token).trans
      (Nat.pow_le_pow_right (by decide) (tokenWord_le_stream tokens token hmem)))
  simpa only [List.length_map,smul_eq_mul] using hsum

end NearQuarticWires.StageFormulaMetadata
