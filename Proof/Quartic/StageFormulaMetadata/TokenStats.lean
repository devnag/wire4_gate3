import Proof.Quartic.StageFormulaMetadata.Packet
import Proof.Quartic.StageLift.ReduceFormula

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex:
the unary syntactic contribution of a postfix power includes its
actual exponent, while every other token contributes one node. -/
def tokenAstSize : Tok → ℕ
  | .pow exponent => exponent+1
  | _ => 1

/-- `lem:print` and `lem:residue`, paper/paper.tex: coefficient normalization changes only
constant payloads in the existing seven-token formula codec. -/
def normalizeToken (modulus : ℕ) : Tok → Tok
  | .const value => .const (value % (modulus:ℤ))
  | token => token

/-- `lem:print`, paper/paper.tex:
normalization preserves the actual postfix operation order. -/
def normalizeTokens (modulus : ℕ) (tokens : List Tok) : List Tok :=
  tokens.map (normalizeToken modulus)

/-- `lem:print`, paper/paper.tex:
the counted syntax contribution is exactly the original formula's
size, including the exponent contribution at every power node. -/
theorem tokenAstSize_toks {arity : ℕ} (formula : Formula arity) :
    ((toks formula).map tokenAstSize).sum = formula.size := by
  induction formula <;>
    simp_all [toks,tokenAstSize,Formula.size,List.sum_append] <;> omega

/-- `lem:print` and `lem:residue`, paper/paper.tex: the normalized token sequence is the
unchanged existing codec of the coefficient-reduced formula. -/
theorem normalizeTokens_toks {arity : ℕ} (modulus : ℕ) (formula : Formula arity) :
    normalizeTokens modulus (toks formula) = toks (StageLift.reduceConstants modulus formula) := by
  induction formula <;>
    simp_all [normalizeTokens,normalizeToken,toks,StageLift.reduceConstants,List.map_append]

/-- `lem:print`, paper/paper.tex:
the actual number of tokens is unchanged by constant normalization. -/
theorem normalizeTokens_length (modulus : ℕ) (tokens : List Tok) :
    (normalizeTokens modulus tokens).length = tokens.length := by
  simp [normalizeTokens]

/-- `lem:print`, paper/paper.tex:
the syntax-size counter is independent of coefficient reduction. -/
theorem normalizeToken_astSize (modulus : ℕ) (token : Tok) :
    tokenAstSize (normalizeToken modulus token) = tokenAstSize token := by
  cases token <;> rfl

/-- `lem:print`, paper/paper.tex:
modulus zero is exact signed-token passthrough, preserving negative
constants instead of sending them to modular coefficient recovery. -/
theorem normalizeTokens_zero (tokens : List Tok) : normalizeTokens 0 tokens = tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      cases token <;> simp_all [normalizeTokens,normalizeToken]

/-- `lem:print`, paper/paper.tex:
the exact constant mode preserves the entire original formula. -/
theorem reduceConstants_zero {arity : ℕ} (formula : Formula arity) :
    StageLift.reduceConstants 0 formula = formula := by
  induction formula <;> simp_all [StageLift.reduceConstants]

end NearQuarticWires.StageFormulaMetadata
