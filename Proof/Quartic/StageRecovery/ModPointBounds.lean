import Proof.Quartic.StageRecovery.ModPointFields
import Proof.Gates.WorkerArith.GuessWordLengths

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: the source formula's
structural workspace hint bounds all binary header field lengths. -/
theorem ModPointRequest.field_bits (r : ModPointRequest) :
    ∀ value ∈ r.fields, natBitLength value ≤ r.source.hint + 2 := by
  have hh := r.source.hint_sufficient
  let H := r.source.arity + r.source.formula.size +
    (formulaWord ⟨r.source.arity, r.source.formula⟩).length + natBitLength r.source.modulus + 10
  have hH : H ≤ r.source.hint + 1 := by
    change H ^ 2 ≤ r.source.hint at hh
    nlinarith
  have hstruct := hH
  dsimp [H] at hstruct
  have hn := tokens_length_le_stream r.source.formula
  have ht : (tokenStream (toks r.source.formula)).length ≤
      (formulaWord ⟨r.source.arity, r.source.formula⟩).length := by
    simp only [formulaWord, NearCubicGates.Close.Interfaces.listWord, List.length_append, tokenStream]
    omega
  have hp : natBitLength r.point ≤ r.source.arity + 1 := by
    apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by omega)
    exact r.point_fit.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := nbl_le_self r.source.hint
  have ha := nbl_le_self r.source.arity
  have hnc := nbl_le_self (toks r.source.formula).length
  intro value hv
  simp only [ModPointRequest.fields, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega

/-- `prop:time`, paper/paper.tex: the actual postfix
stack and token counters fit the structural workspace hint. -/
theorem ModPointRequest.execution_bounds (C : Ctx) (r : ModPointRequest)
    (hwidth : 64 * (r.source.hint + 1) ≤ C.Wd) :
    (∀ value ∈ r.fields, natBitLength value + 2 ≤ C.Wd) ∧
      formulaTokenBound r.source.formula + 5 ≤ C.Wd ∧
      (toks r.source.formula).length < 2 ^ C.Wd ∧
      r.source.modulus ^ ((toks r.source.formula).length + 3) ≤ 2 ^ C.Wd := by
  have hb := r.source.core_width
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hn : (toks r.source.formula).length ≤ formulaTokenBound r.source.formula := by
    have := tokens_length_le_stream r.source.formula
    dsimp [formulaTokenBound]
    omega
  refine ⟨fun value hv => by have := r.field_bits value hv; omega,
    by omega, by omega, ?_⟩
  calc r.source.modulus ^ ((toks r.source.formula).length + 3) ≤
      (2 ^ natBitLength r.source.modulus) ^ ((toks r.source.formula).length + 3) :=
        Nat.pow_le_pow_left (lt_natBitLength _).le _
    _ = 2 ^ (natBitLength r.source.modulus * ((toks r.source.formula).length + 3)) := by
      rw [pow_mul]
    _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) (by
      rw [Nat.mul_comm]
      omega)

/-- `lem:residue`, paper/paper.tex: the point evaluator's
literal nonnegative result is the exact general-modulus formula residue. -/
def ModPointRequest.value (r : ModPointRequest) : ℕ :=
  (modAlg r.source.modulus r.point).eval r.source.formula

/-- `lem:residue`, paper/paper.tex: the internal point
result agrees with the original Boolean formula modulo the actual
recovery modulus, without an integer approximation. -/
theorem ModPointRequest.value_eq (r : ModPointRequest) :
    (r.value : ℤ) = r.source.formula.eval
      (NearCubicGates.Close.Tabulator.boolPoint (ind (setOf r.source.arity r.point))) %
        (r.source.modulus : ℤ) :=
  modAlg_eval _ _ (by have := r.source.modulus_ge_two; omega) _

/-- `prop:time`, paper/paper.tex: the emitted reduced
point value fits the actual binary width of the recovery modulus. -/
theorem ModPointRequest.value_bits (r : ModPointRequest) :
    natBitLength r.value ≤ natBitLength r.source.modulus := by
  have hv := (modAlg r.source.modulus r.point).eval_lt
    (modAlg_closed _ _ (by have := r.source.modulus_ge_two; omega)) r.source.formula
  apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by unfold natBitLength; omega)
  exact hv.trans (lt_natBitLength _)

end NearQuarticWires.StageRecovery
