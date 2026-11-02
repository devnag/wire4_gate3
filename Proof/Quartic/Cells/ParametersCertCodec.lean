import Proof.Quartic.Cells.ParametersCertNativeBits
import Proof.Quartic.StageLift.FormulaBytes
import Proof.Quartic.StageLift.FormulaSize

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: an explicit bit
bound on every literal integer leaf of the original Formula AST. -/
def formulaConstantBits {V : ℕ} (L : ℕ) : Formula V → Prop
  | .const z => Nat.size z.natAbs ≤ L
  | .var _ => True
  | .add f g => formulaConstantBits L f ∧ formulaConstantBits L g
  | .neg f => formulaConstantBits L f
  | .sub f g => formulaConstantBits L f ∧ formulaConstantBits L g
  | .mul f g => formulaConstantBits L f ∧ formulaConstantBits L g
  | .pow f _ => formulaConstantBits L f

/-- `lem:print`, paper/paper.tex: the actual raw
constant codec is bounded by its literal leaf bit height. -/
theorem cert_constant_token_bytes (z : ℤ) (L : ℕ) (hz : Nat.size z.natAbs ≤ L) :
    (tokWord (.const z)).length ≤ 2 * (L + 1) + 7 := by
  have hlt : z.natAbs < 2 ^ (L + 1) := (Nat.size_le.mp hz).trans_le
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ L))
  have hn := NearCubicGates.Close.Cells.nbl_le_of_lt hlt (by omega)
  rw [StageLift.constant_token_bytes]
  omega

/-- `lem:print`, paper/paper.tex: the raw
postfix token stream has its actual leaf-bit and unary-exponent
cost, without replacing the Formula by a modular reduction. -/
theorem cert_raw_formula_token_bytes {V : ℕ} (F : Formula V) (L : ℕ)
    (hbits : formulaConstantBits L F) :
    StageLift.formulaTokenBytes F ≤ (2 * (natBitLength V + L + 1) + 15) * F.size := by
  let K := 2 * (natBitLength V + L + 1) + 15
  have hK : 15 ≤ K := by dsimp only [K]; omega
  change StageLift.formulaTokenBytes F ≤ K * F.size
  revert hbits
  induction F with
  | const z =>
    intro hbits
    have hb := cert_constant_token_bytes z L hbits
    simpa only [StageLift.formulaTokenBytes, toks, List.flatMap_singleton,
      Formula.size, Nat.mul_one] using hb.trans (by dsimp only [K]; omega)
  | var atom =>
    intro _
    have hb := StageLift.codec_nbl_mono atom.isLt.le
    have ht : (natWord 1).length = 3 := by decide
    simp only [StageLift.formulaTokenBytes, toks, List.flatMap_singleton, tokWord,
      List.length_append, ht, NearCubicGates.Close.Cells.natWord_length, Formula.size, Nat.mul_one]
    dsimp only [K]
    omega
  | add f g ihf ihg =>
    intro hbits
    have hf := ihf hbits.1
    have hg := ihg hbits.2
    have ht : (tokWord .add).length = 5 := by decide
    simp only [StageLift.formulaTokenBytes, toks, List.flatMap_append,
      List.flatMap_singleton, List.length_append, ht, Formula.size]
    dsimp only [StageLift.formulaTokenBytes] at hf hg
    nlinarith only [hf, hg, hK]
  | sub f g ihf ihg =>
    intro hbits
    have hf := ihf hbits.1
    have hg := ihg hbits.2
    have ht : (tokWord .sub).length = 7 := by decide
    simp only [StageLift.formulaTokenBytes, toks, List.flatMap_append,
      List.flatMap_singleton, List.length_append, ht, Formula.size]
    dsimp only [StageLift.formulaTokenBytes] at hf hg
    nlinarith only [hf, hg, hK]
  | mul f g ihf ihg =>
    intro hbits
    have hf := ihf hbits.1
    have hg := ihg hbits.2
    have ht : (tokWord .mul).length = 7 := by decide
    simp only [StageLift.formulaTokenBytes, toks, List.flatMap_append,
      List.flatMap_singleton, List.length_append, ht, Formula.size]
    dsimp only [StageLift.formulaTokenBytes] at hf hg
    nlinarith only [hf, hg, hK]
  | neg f ih =>
    intro hbits
    have hf := ih hbits
    have ht : (tokWord .neg).length = 5 := by decide
    simp only [StageLift.formulaTokenBytes, toks, List.flatMap_append,
      List.flatMap_singleton, List.length_append, ht, Formula.size]
    dsimp only [StageLift.formulaTokenBytes] at hf
    nlinarith only [hf, hK]
  | pow f exponent ih =>
    intro hbits
    have hf := ih hbits
    have he := NearCubicGates.Close.Cells.nbl_le_self exponent
    have ht : (natWord 6).length = 7 := by decide
    have hm := Nat.mul_le_mul_right (exponent + 1) hK
    simp only [StageLift.formulaTokenBytes, toks, List.flatMap_append,
      List.flatMap_singleton, List.length_append, tokWord, ht,
      NearCubicGates.Close.Cells.natWord_length, Formula.size]
    dsimp only [StageLift.formulaTokenBytes] at hf
    nlinarith only [hf, he, hm]

/-- `lem:print`, paper/paper.tex: the complete
raw canonical Formula word includes both physical headers as
well as every original token and integer payload. -/
theorem cert_raw_formula_word_bytes {V : ℕ} (F : Formula V) (L : ℕ)
    (hbits : formulaConstantBits L F) :
    (formulaWord ⟨V, F⟩).length ≤
      (2 * (natBitLength V + L + 1) + 17) * F.size + 2 * natBitLength V + 4 := by
  have hL := cert_raw_formula_token_bytes F L hbits
  have hN := StageLift.formula_tokens_le_size F
  have hn := NearCubicGates.Close.Cells.nbl_le_self (toks F).length
  simp only [formulaWord, NearCubicGates.Close.Interfaces.listWord, List.length_append,
    NearCubicGates.Close.Cells.natWord_length]
  dsimp only [StageLift.formulaTokenBytes] at hL
  nlinarith only [hL, hN, hn]

end NearQuarticWires.Cells.ParameterArithmetic
