import Proof.Quartic.StageMainMask.CompiledEntry

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain

private theorem scalar_parts (w a e t n : ℕ) :
    let S := w + a + e + t + 128 + 10 + n + 1000
    1 ≤ S ∧ 128 ≤ S ∧ 10 ≤ S ∧ t ≤ S ∧ a ≤ S ∧ e ≤ S ∧ n + 2 ≤ S ∧ w ≤ S := by
  dsimp
  omega

private theorem compiler_arithmetic (W I S : ℕ) (hS : 1 ≤ S) (hW : W ≤ S) (hI : I ≤ S) :
    10000 * S ^ 2 * (1000 * W + I + 1) ≤ 11000000 * S ^ 3 := by
  have hsum : 1000 * W + I + 1 ≤ 1002 * S := by omega
  calc
    _ ≤ 10000 * S ^ 2 * (1002 * S) := Nat.mul_le_mul_left _ hsum
    _ ≤ _ := by ring_nf; omega

private theorem scale_arithmetic (W a e t n : ℕ)
    (hW : W ≤ (a * 4 ^ e) * (n + 1) ^ e) :
    W + a + e + t + 128 + 10 + n + 1000 ≤
      (a * 4 ^ e + a + e + t + 128 + 10 + 1002) * (n + 1) ^ (e + 1) := by
  have hp : (n + 1) ^ e ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have hn : n + 1 ≤ (n + 1) ^ (e + 1) := Nat.le_self_pow (by omega) _
  have hconst : 1 ≤ (n + 1) ^ (e + 1) := Nat.pow_pos (Nat.succ_pos _)
  have hw' := hW.trans (Nat.mul_le_mul_left (a * 4 ^ e) hp)
  nlinarith

/-- `prop:time`, paper/paper.tex: the complete
ordinary compiler scale includes the actual arity-header reservation,
fixed program tape banks, scalar/store dimensions and source header. -/
noncomputable def entryCompilerScale (B1 B2 n : ℕ) : ℕ :=
  (entrySizes B1 B2).W (1 + natBitLength n) + ((entrySizePair B1 B2).1 + 64) +
    (entrySizePair B1 B2).2 + TSK (entryCallee B1 B2) + VV + MM + n + 1000

/-- `prop:time`, paper/paper.tex: fixed machine
dimensions and the arity-header reservation have a single original-
arity polynomial coefficient for the actual compiled Entry machine. -/
noncomputable def entryCompilerCoefficient (B1 B2 : ℕ) : ℕ :=
  ((entrySizePair B1 B2).1 + 64) * 4 ^ (entrySizePair B1 B2).2 +
    (entrySizePair B1 B2).1 + 64 + (entrySizePair B1 B2).2 +
    TSK (entryCallee B1 B2) + VV + MM + 1002

/-- `prop:time`, paper/paper.tex: the complete
actual ordinary Entry budget is bounded cubically in its funded native
width and fixed compiler dimensions, including all cold helper banks. -/
theorem entryBudget_scale {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    entryBudget r ≤ 11000000 * (entryCompilerScale B1 B2 r.call.n) ^ 3 := by
  let W := (entrySizes B1 B2).W (1 + natBitLength r.call.n)
  let S := entryCompilerScale B1 B2 r.call.n
  have hparts := scalar_parts W ((entrySizePair B1 B2).1 + 64)
    (entrySizePair B1 B2).2 (TSK (entryCallee B1 B2)) r.call.n
  change 1 ≤ S ∧ VV ≤ S ∧ MM ≤ S ∧ TSK (entryCallee B1 B2) ≤ S ∧
    (entrySizePair B1 B2).1 + 64 ≤ S ∧ (entrySizePair B1 B2).2 ≤ S ∧
    r.call.n + 2 ≤ S ∧ W ≤ S at hparts
  rcases hparts with ⟨hS, hV, hM, hK, ha, hd, hn, hw⟩
  have hhead : leadOnes (entryWord r) ≤ S := by
    rw [entryWord_header]
    have hbit := NearCubicGates.Close.Dispatch.natBitLength_le_succ r.call.n
    omega
  have hwidth : (entrySizes B1 B2).W (leadOnes (entryWord r)) ≤ S := by
    rw [entryWord_header]
    exact hw
  have hcompile : entryBudget r ≤ 10000 * S ^ 2 * (entryStepLimit r + (entryWord r).length + 1) := by
    unfold entryBudget
    apply StageMain.Runtime.langBudget_le
    · exact hS
    · exact hV
    · exact hM
    · exact hK
    · exact ha
    · exact hd
    · exact ha
    · exact hd
    · exact ha
    · exact hd
    · exact hhead
    · exact hwidth
    · rw [(entrySizes_reserves B1 B2 _).1]
      exact hwidth
    · rw [(entrySizes_reserves B1 B2 _).2]
      exact hwidth
  have hstep : entryStepLimit r = 1000 * W := by
    unfold entryStepLimit
    rw [entryWord_header]
  have hinput : (entryWord r).length ≤ S := by
    have hr := entrySizes_resources r
    rw [entryWord_header] at hr
    have hh := entryResources_scale r
    have hl := (entrySourceScale_bounds r).2.1
    change entryResources r ≤ W at hr
    omega
  rw [hstep] at hcompile
  exact hcompile.trans (compiler_arithmetic W (entryWord r).length S hS hw hinput)

/-- `prop:time`, paper/paper.tex: the actual
Entry compiler scale is polynomial in the original arity, with all
source and call reservations determined by the literal arity header. -/
theorem entryCompilerScale_polynomial (B1 B2 n : ℕ) :
    entryCompilerScale B1 B2 n ≤ entryCompilerCoefficient B1 B2 *
      (n + 1) ^ ((entrySizePair B1 B2).2 + 1) := by
  have hw := StageMain.Runtime.header_power_le ((entrySizePair B1 B2).1 + 64)
    (entrySizePair B1 B2).2 n
  have hh := scale_arithmetic ((entrySizes B1 B2).W (1 + natBitLength n))
    ((entrySizePair B1 B2).1 + 64) (entrySizePair B1 B2).2 (TSK (entryCallee B1 B2)) n hw
  simpa only [entryCompilerScale, entryCompilerCoefficient, Nat.add_assoc] using hh

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the complete actual Entry ordinary
machine has one fixed original-arity polynomial budget, uniformly over
all original source calls, witnesses, columns and sampled field values. -/
theorem entryBudget_arity (B1 B2 : ℕ) :
    ∃ K d : ℕ, ∀ r : EntryRequest B1 B2, entryBudget r ≤ K * (r.call.n + 1) ^ d := by
  refine ⟨11000000 * (entryCompilerCoefficient B1 B2) ^ 3,
    3 * ((entrySizePair B1 B2).2 + 1), ?_⟩
  intro r
  calc
    _ ≤ 11000000 * (entryCompilerScale B1 B2 r.call.n) ^ 3 := entryBudget_scale r
    _ ≤ 11000000 * (entryCompilerCoefficient B1 B2 *
        (r.call.n + 1) ^ ((entrySizePair B1 B2).2 + 1)) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (entryCompilerScale_polynomial B1 B2 r.call.n) 3)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm ((entrySizePair B1 B2).2 + 1) 3]; ring

end NearQuarticWires.StageMainMask
