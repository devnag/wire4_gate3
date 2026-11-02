import Proof.Quartic.StageFormulaMetadata.TokenBounds

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream)

/-- `lem:print`, paper/paper.tex: every physical
constant-sign field has one binary payload bit in either mode. -/
theorem normalizedSign_bits (modulus : ℕ) (negative : Bool) :
    natBitLength (normalizedSign modulus negative)=1 := by
  unfold normalizedSign
  split
  · cases negative <;> simp [natBitLength]
  · simp [natBitLength]

/-- `prop:time`, paper/paper.tex: normalization
can enlarge one constant's codec only by the actual modulus width. -/
theorem normalizedWord_length_le (modulus : ℕ) (token : Tok)
    (hmode : modulus=0 ∨ 2 ≤ modulus) :
    (tokWord (normalizeToken modulus token)).length≤(tokWord token).length+2*natBitLength modulus := by
  cases token with
  | const value =>
      have hmag:=normalizedMagnitude_bits modulus value.natAbs (decide (value<0)) hmode
      have hsign : natBitLength (decide (value<0)).toNat=1 := by
        by_cases h : value<0 <;> simp [h,natBitLength]
      simp only [normalizeToken,tokWord,normalizedInteger_fields modulus value hmode,
        integerWord_fields,List.length_append,natWord_length,normalizedSign_bits,hsign]
      omega
  | var _ | add | neg | sub | mul | pow _ =>
      simp only [normalizeToken]
      omega

/-- `prop:time`, paper/paper.tex: the actual
normalized output length is at most the scanned source length plus
one binary modulus-width allowance per physically read token. -/
theorem normalizedStream_length_le (modulus : ℕ) (tokens : List Tok)
    (hmode : modulus=0 ∨ 2 ≤ modulus) :
    (tokenStream (normalizeTokens modulus tokens)).length≤
      (tokenStream tokens).length+tokens.length*(2*natBitLength modulus) := by
  induction tokens with
  | nil => simp [normalizeTokens,tokenStream]
  | cons token tokens ih =>
      have ht:=normalizedWord_length_le modulus token hmode
      simp only [normalizeTokens,List.map_cons,tokenStream,List.flatMap_cons,List.length_append,
        List.length_cons] at ih ⊢
      nlinarith

/-- `prop:time`, paper/paper.tex: one actual
token's source clock is linear in its original codec and modulus bits. -/
theorem metadataTokenCost_le (modulus : ℕ) (token : Tok)
    (hmode : modulus=0 ∨ 2 ≤ modulus) :
    metadataTokenCost modulus token≤1000*((tokWord token).length+natBitLength modulus+1) := by
  have hwidth:=tokenFieldWidth_le_word token
  have htag : natBitLength (tokenTag token)≤3 := by
    cases token <;> norm_num [tokenTag,natBitLength]
  have hseven:=tokenTag_lt_seven token
  cases token with
  | const value =>
      have hm:=normalizedMagnitude_bits modulus value.natAbs (decide (value<0)) hmode
      simp only [metadataTokenCost,payloadCost,tokenFieldWidth] at *
      omega
  | var _ | add | neg | sub | mul | pow _ =>
      simp only [metadataTokenCost,payloadCost,tokenFieldWidth] at *
      omega

/-- `prop:time`, paper/paper.tex: one entire
physical token pass has an explicit quadratic bound in its actual
source length and the source modulus's binary width. -/
theorem metadataLoopCost_le (modulus : ℕ) (tokens : List Tok)
    (hmode : modulus=0 ∨ 2 ≤ modulus) :
    metadataLoopCost modulus tokens≤1002*((tokenStream tokens).length+
      tokens.length*(natBitLength modulus+1))+2 := by
  induction tokens with
  | nil => simp [metadataLoopCost,tokenStream]
  | cons token tokens ih =>
      have ht:=metadataTokenCost_le modulus token hmode
      simp only [metadataLoopCost,List.map_cons,List.sum_cons,tokenStream,List.flatMap_cons,
        List.length_append,List.length_cons] at ih ⊢
      nlinarith

end NearQuarticWires.StageFormulaMetadata
