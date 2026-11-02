import Proof.Quartic.StageRecovery.ModLoop
import Proof.Quartic.StageRecovery.ModFormulaRequest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the literal formula
and its unary exponent sizes bound every modular token operation. -/
def formulaTokenBound {V : ℕ} (formula : Formula V) : ℕ :=
  V + formula.size + (tokenStream (toks formula)).length + 10

/-- `lem:print`, paper/paper.tex: every constant height,
atom index and unary power workload is bounded by the actual formula
codec and syntactic size, without any raw polynomial-value bound. -/
theorem tokenBound_le_formula {V : ℕ} (formula : Formula V) :
    ∀ token ∈ toks formula, tokenBound token ≤ formulaTokenBound formula := by
  induction formula with
  | const value =>
      intro token ht
      have he : token = .const value := by simpa [toks] using ht
      subst token
      simp only [formulaTokenBound, Formula.size, toks, tokenStream, List.flatMap_singleton,
        tokWord, NearCubicGates.Close.Interfaces.intWord, List.length_append,
        NearCubicGates.Close.Cells.natWord_length, tokenBound]
      split <;> omega
  | var atom =>
      intro token ht
      have he : token = .var atom.val := by simpa [toks] using ht
      subst token
      have ha := atom.isLt
      dsimp only [tokenBound, formulaTokenBound, Formula.size]
      omega
  | add left right ihl ihr =>
      intro token ht
      simp only [toks, List.mem_append, List.mem_singleton] at ht
      simp only [formulaTokenBound, toks, tokenStream, List.flatMap_append,
        List.length_append, List.flatMap_singleton, Formula.size]
      rcases ht with (ht | ht) | rfl
      · have := ihl token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · have := ihr token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · simp [tokenBound]
  | sub left right ihl ihr =>
      intro token ht
      simp only [toks, List.mem_append, List.mem_singleton] at ht
      simp only [formulaTokenBound, toks, tokenStream, List.flatMap_append,
        List.length_append, List.flatMap_singleton, Formula.size]
      rcases ht with (ht | ht) | rfl
      · have := ihl token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · have := ihr token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · simp [tokenBound]
  | mul left right ihl ihr =>
      intro token ht
      simp only [toks, List.mem_append, List.mem_singleton] at ht
      simp only [formulaTokenBound, toks, tokenStream, List.flatMap_append,
        List.length_append, List.flatMap_singleton, Formula.size]
      rcases ht with (ht | ht) | rfl
      · have := ihl token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · have := ihr token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · simp [tokenBound]
  | neg child ih =>
      intro token ht
      simp only [toks, List.mem_append, List.mem_singleton] at ht
      simp only [formulaTokenBound, toks, tokenStream, List.flatMap_append,
        List.length_append, List.flatMap_singleton, Formula.size]
      rcases ht with ht | rfl
      · have := ih token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · simp [tokenBound]
  | pow child exponent ih =>
      intro token ht
      simp only [toks, List.mem_append, List.mem_singleton] at ht
      simp only [formulaTokenBound, toks, tokenStream, List.flatMap_append,
        List.length_append, List.flatMap_singleton, Formula.size]
      rcases ht with ht | rfl
      · have := ih token ht; dsimp [formulaTokenBound, tokenStream] at this; omega
      · simp [tokenBound]; omega

/-- `lem:print`, paper/paper.tex: all actual formula
tokens are counted by their literal serialized token stream. -/
theorem tokens_length_le_stream {V : ℕ} (formula : Formula V) :
    (toks formula).length ≤ (tokenStream (toks formula)).length := by
  unfold tokenStream
  rw [List.length_flatMap]
  calc (toks formula).length = ((toks formula).map fun _ => 1).sum := by simp
    _ ≤ ((toks formula).map fun token => (tokWord token).length).sum := by
      apply List.sum_le_sum
      intro token _
      rw [tokWord_eq, List.length_append, natWord_length]
      omega

/-- `lem:print`, paper/paper.tex: token workspace and
depth fit the literal modular formula request's structural hint. -/
theorem ModFormulaRequest.core_width (r : ModFormulaRequest) :
    formulaTokenBound r.formula + 5 ≤ 4 * (r.hint + 1) ∧
      ((toks r.formula).length + 3) * natBitLength r.modulus ≤ 4 * (r.hint + 1) := by
  let L := (formulaWord ⟨r.arity, r.formula⟩).length
  have ht : (tokenStream (toks r.formula)).length ≤ L := by
    simp only [L, formulaWord, NearCubicGates.Close.Interfaces.listWord,
      List.length_append, tokenStream]
    omega
  have hn := tokens_length_le_stream r.formula
  have hh := r.hint_sufficient
  have hbits : 1 ≤ natBitLength r.modulus := by unfold natBitLength; omega
  let H := r.arity + r.formula.size + L + natBitLength r.modulus + 10
  change H ^ 2 ≤ r.hint at hh
  have hH : H ≤ r.hint + 1 := by nlinarith
  constructor
  · dsimp only [formulaTokenBound]
    have he : r.arity + r.formula.size + (tokenStream (toks r.formula)).length + 10 ≤ H := by
      dsimp [H]; omega
    omega
  · have hleft : (toks r.formula).length + 3 ≤ H := by dsimp [H]; omega
    have hright : natBitLength r.modulus ≤ H := by dsimp [H]; omega
    have hp := Nat.mul_le_mul hleft hright
    rw [← pow_two] at hp
    exact hp.trans (hh.trans (by omega))

end NearQuarticWires.StageRecovery
