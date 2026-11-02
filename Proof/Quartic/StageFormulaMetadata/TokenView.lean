import Proof.Quartic.StageFormulaMetadata.TokenStats
import Proof.Quartic.StageFormulaMetadata.ConstantCodec

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (intWord)
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the literal
original seven-token tag is decoded before its following payload. -/
def tokenTag : Tok→ℕ
  | .const _=>0
  | .var _=>1
  | .add=>2
  | .neg=>3
  | .sub=>4
  | .mul=>5
  | .pow _=>6

/-- `lem:print`, paper/paper.tex: only constants,
atom indices and powers have a payload after the token's tag. -/
def tokenTail : Tok→List Bool
  | .const value=>intWord value
  | .var index=>natWord index
  | .pow exponent=>natWord exponent
  | _=>[]

/-- `lem:print`, paper/paper.tex: the binary
payload decoder needs only the width of its actual source field. -/
def tokenFieldWidth : Tok→ℕ
  | .const value=>natBitLength value.natAbs
  | .var index=>natBitLength index
  | .pow exponent=>natBitLength exponent
  | _=>1

/-- `lem:print`, paper/paper.tex: token dispatch
uses exactly the original tag and payload byte decomposition. -/
theorem tokenWord_eq (token : Tok) :
    tokWord token=natWord (tokenTag token)++tokenTail token := by
  cases token <;> simp [tokWord,tokenTag,tokenTail]

/-- `lem:print`, paper/paper.tex: constant
normalization changes no tag or operation selection. -/
theorem normalizedTag (modulus : ℕ) (token : Tok) :
    tokenTag (normalizeToken modulus token)=tokenTag token := by cases token <;> rfl

/-- `lem:print`, paper/paper.tex: all seven
literal tags fit the actual constant-size dispatch tree. -/
theorem tokenTag_lt_seven (token : Tok) : tokenTag token<7 := by cases token <;> simp [tokenTag]

end NearQuarticWires.StageFormulaMetadata
