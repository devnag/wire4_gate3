import Proof.Quartic.StageFormulaMetadata.Output
import Proof.Gates.Cells.Mac

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual
Formula request length is computed from its two natural fields and
its measured normalized postfix payload length. -/
def formulaLengthValue (arity count payloadLength : ℕ) : ℕ :=
  (natWord arity).length+(natWord count).length+payloadLength

/-- `prop:time`, paper/paper.tex: the inner
compiler workspace magnitude uses actual syntax and codec counters. -/
def hintBaseValue (arity syntaxSize count payloadLength modulus : ℕ) : ℕ :=
  arity+syntaxSize+formulaLengthValue arity count payloadLength+natBitLength modulus+10

/-- `prop:time`, paper/paper.tex: the actual
inner hint is the square of its source-derived binary magnitude. -/
def hintValue (arity syntaxSize count payloadLength modulus : ℕ) : ℕ :=
  hintBaseValue arity syntaxSize count payloadLength modulus^2

/-- `prop:time`, paper/paper.tex: the outer
family hint includes its original finite-degree and arity reserve. -/
def setupValue (degree arity syntaxSize count payloadLength modulus : ℕ) : ℕ :=
  hintValue arity syntaxSize count payloadLength modulus+(degree+arity+10)^2

/-- `lem:print`, paper/paper.tex: the physical
formula-byte arithmetic agrees with the exact counted request word. -/
theorem formulaLengthValue_eq (arity modulus : ℕ) (tokens : List NearCubicGates.Close.Interfaces.Formats.Tok) :
    formulaLengthValue arity tokens.length (normalizedPayload modulus tokens).length=
      (countedFormulaWord arity modulus tokens).length := by
  simp only [formulaLengthValue,countedFormulaWord,List.length_append]

/-- `prop:time`, paper/paper.tex: the register
arithmetic computes the exact frozen compiler hint. -/
theorem hintValue_eq (arity modulus : ℕ) (tokens : List NearCubicGates.Close.Interfaces.Formats.Tok) :
    hintValue arity (tokens.map tokenAstSize).sum tokens.length (normalizedPayload modulus tokens).length modulus=
      countedHint arity modulus tokens := by
  rw [hintValue,hintBaseValue,formulaLengthValue_eq]
  rfl

/-- `prop:time`, paper/paper.tex: every partial
hint sum is below the final setup reserve, including actual field
lengths and the complete modulus codec. -/
theorem hint_partial_bounds (degree arity syntaxSize count payloadLength modulus : ℕ) :
    let formulaLength:=formulaLengthValue arity count payloadLength
    let base:=hintBaseValue arity syntaxSize count payloadLength modulus
    let setup:=setupValue degree arity syntaxSize count payloadLength modulus
    (natWord arity).length≤formulaLength ∧ (natWord count).length≤formulaLength ∧
    formulaLength≤base ∧ base≤base^2 ∧ (natWord modulus).length≤base^2 ∧
    base^2 ≤ setup ∧ (degree+arity+10)^2 ≤ setup ∧ degree+arity+10≤(degree+arity+10)^2 ∧
    10 ≤ setup := by
  dsimp only
  have hb : 10≤hintBaseValue arity syntaxSize count payloadLength modulus := by
    unfold hintBaseValue
    omega
  have hq : natBitLength modulus+10≤hintBaseValue arity syntaxSize count payloadLength modulus := by
    unfold hintBaseValue
    omega
  have hd : 10≤degree+arity+10 := by omega
  dsimp only [setupValue,hintValue,hintBaseValue,formulaLengthValue] at *
  simp only [natWord_length] at *
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  · nlinarith

end NearQuarticWires.StageFormulaMetadata
