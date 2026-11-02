import Proof.Quartic.StageRecovery.TermsCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: the normalized
Formula's actual size, complete codec and modulus bits determine the
small structural magnitude used by its physical input formatter. -/
def ModFormulaRequest.syntaxMagnitude (r : ModFormulaRequest) : ℕ :=
  r.arity + r.formula.size + (formulaWord ⟨r.arity, r.formula⟩).length +
    natBitLength r.modulus + 10

/-- `prop:time`, paper/paper.tex: the whole compiler
structural magnitude adds the serialized degree bound once to the
actual normalized Formula magnitude. -/
def FamilyCompileRequest.syntaxMagnitude (r : FamilyCompileRequest) : ℕ :=
  r.source.syntaxMagnitude + r.degree + 1

/-- `prop:time`, paper/paper.tex: the actual chosen
squared Formula hint and squared finite-family dimensions are bounded
by one common squared syntax magnitude, without a family-count factor. -/
theorem FamilyCompileRequest.setupHint_syntax_le (r : FamilyCompileRequest)
    (hhint : r.source.hint = r.source.syntaxMagnitude ^ 2) :
    r.setupHint + 1 ≤ 3 * r.syntaxMagnitude ^ 2 := by
  have hs : r.source.syntaxMagnitude ≤ r.syntaxMagnitude := by
    unfold FamilyCompileRequest.syntaxMagnitude
    omega
  have hd : r.degree + r.source.arity + 10 ≤ r.syntaxMagnitude := by
    unfold FamilyCompileRequest.syntaxMagnitude ModFormulaRequest.syntaxMagnitude
    omega
  have hp : 1 ≤ r.syntaxMagnitude ^ 2 := by
    have hpos : 0 < r.syntaxMagnitude ^ 2 := by
      unfold FamilyCompileRequest.syntaxMagnitude
      positivity
    omega
  have hs2 := Nat.pow_le_pow_left hs 2
  have hd2 := Nat.pow_le_pow_left hd 2
  unfold FamilyCompileRequest.setupHint
  rw [hhint]
  omega

/-- `prop:time`, paper/paper.tex: the actual cold
compiler's physical cost has the squared family census and sixth power
of the real normalized syntax magnitude for the formatter's chosen hint. -/
theorem FamilyCompileRequest.modularTermsBudget_syntax_le (r : FamilyCompileRequest)
    (hhint : r.source.hint = r.source.syntaxMagnitude ^ 2) :
    r.modularTermsBudget ≤ 27 * 10 ^ 22 * (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * r.syntaxMagnitude ^ 6 := by
  have hh := r.setupHint_syntax_le hhint
  have hcube : (r.setupHint + 1) ^ 3 ≤ 27 * r.syntaxMagnitude ^ 6 := by
    calc (r.setupHint + 1) ^ 3 ≤ (3 * r.syntaxMagnitude ^ 2) ^ 3 := Nat.pow_le_pow_left hh _
      _ = _ := by ring
  calc r.modularTermsBudget ≤ 10 ^ 22 * (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) ^ 3 := r.modularTermsBudget_le
    _ ≤ 10 ^ 22 * (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (27 * r.syntaxMagnitude ^ 6) :=
        Nat.mul_le_mul_left _ hcube
    _ = _ := by ring

/-- `prop:time`, paper/paper.tex: both real Formula
codec headers are paid by its arity and actual token-byte count. -/
theorem ModFormulaRequest.formulaWord_length_le (r : ModFormulaRequest) :
    (formulaWord ⟨r.arity, r.formula⟩).length ≤
      2 * r.arity + 3 * (tokenStream (toks r.formula)).length + 6 := by
  have hV := nbl_le_self r.arity
  have hN := nbl_le_self (toks r.formula).length
  have htok := tokens_length_le_stream r.formula
  simp only [formulaWord, NearCubicGates.Close.Interfaces.listWord, tokenStream,
    List.length_append, NearCubicGates.Close.Cells.natWord_length]
  dsimp [tokenStream] at htok
  omega

/-- `prop:time`, paper/paper.tex: an actual
normalized Formula-size-and-byte bound gives a bound for the complete
compiler syntax magnitude, including both literal codec headers. -/
theorem FamilyCompileRequest.syntaxMagnitude_le (r : FamilyCompileRequest) (B X : ℕ)
    (hbytes : r.source.formula.size + (tokenStream (toks r.source.formula)).length ≤
      B * (r.source.arity + 1) ^ (X + 1)) :
    r.syntaxMagnitude ≤
      (3 * B + 3 * r.source.arity + r.degree + natBitLength r.source.modulus + 20) *
        (r.source.arity + 1) ^ (X + 1) := by
  let P := (r.source.arity + 1) ^ (X + 1)
  let C := 3 * r.source.arity + r.degree + natBitLength r.source.modulus + 20
  have hp : 1 ≤ P := by
    have hpos : 0 < P := by dsimp [P]; positivity
    omega
  have hc : C ≤ C * P := Nat.le_mul_of_pos_right _ hp
  have hcodec := r.source.formulaWord_length_le
  change r.source.formula.size + (tokenStream (toks r.source.formula)).length ≤ B * P at hbytes
  unfold FamilyCompileRequest.syntaxMagnitude ModFormulaRequest.syntaxMagnitude
  change _ ≤ (3 * B + 3 * r.source.arity + r.degree + natBitLength r.source.modulus + 20) * P
  dsimp [C] at hc
  nlinarith

/-- `prop:time`, paper/paper.tex: the actual bounded
support family has at most the original sharp degree census. -/
theorem FamilyCompileRequest.family_census (r : FamilyCompileRequest) :
    (famPairs r.source.arity r.degree).length ≤ (r.source.arity + 1) ^ r.degree := by
  have h := fam_length_le r.source.arity r.degree
  rw [fam_eq_pairs, List.length_map] at h
  exact h

/-- `prop:time`, paper/paper.tex: combining the
physical compiler budget with the literal normalized syntax bound gives
the exact exponent `2D+6X+6`, with no extra native tuple-census factor. -/
theorem FamilyCompileRequest.modularTermsBudget_exponent_le (r : FamilyCompileRequest)
    (B X : ℕ) (hhint : r.source.hint = r.source.syntaxMagnitude ^ 2)
    (hsize : r.syntaxMagnitude ≤ B * (r.source.arity + 1) ^ (X + 1)) :
    r.modularTermsBudget ≤ 4 * 27 * 10 ^ 22 * (TSK packetCallee + 10) * B ^ 6 *
      (r.source.arity + 1) ^ (2 * r.degree + 6 * X + 6) := by
  let V := r.source.arity + 1
  let M := (famPairs r.source.arity r.degree).length
  have hp : 1 ≤ V ^ r.degree := by
    have hpos : 0 < V ^ r.degree := by dsimp [V]; positivity
    omega
  have hm : M + 1 ≤ 2 * V ^ r.degree := by have h := r.family_census; change M ≤ V ^ r.degree at h; omega
  have hm2 : (M + 1) ^ 2 ≤ 4 * V ^ (2 * r.degree) := by
    calc (M + 1) ^ 2 ≤ (2 * V ^ r.degree) ^ 2 := Nat.pow_le_pow_left hm _
      _ = _ := by rw [mul_pow, ← pow_mul]; congr 1; ring
  have hs6 : r.syntaxMagnitude ^ 6 ≤ B ^ 6 * V ^ (6 * X + 6) := by
    calc r.syntaxMagnitude ^ 6 ≤ (B * V ^ (X + 1)) ^ 6 := Nat.pow_le_pow_left hsize _
      _ = _ := by rw [mul_pow, ← pow_mul]; congr 1; congr 1; omega
  calc r.modularTermsBudget ≤ 27 * 10 ^ 22 * (TSK packetCallee + 10) *
      (M + 1) ^ 2 * r.syntaxMagnitude ^ 6 := r.modularTermsBudget_syntax_le hhint
    _ ≤ 27 * 10 ^ 22 * (TSK packetCallee + 10) *
      (4 * V ^ (2 * r.degree)) * (B ^ 6 * V ^ (6 * X + 6)) := by gcongr
    _ = _ := by
      rw [show 2 * r.degree + 6 * X + 6 = 2 * r.degree + (6 * X + 6) by omega, pow_add]
      ring

end NearQuarticWires.StageRecovery
