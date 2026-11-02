import Proof.Quartic.StageResize.WordFunction
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CellsPack (Gof)

theorem bitLength_le (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength
  have h := Nat.log_le_self 2 v
  omega

/-- `prop:time`, paper/paper.tex: the actual
input is linear in the two fixed field widths, including zero widths. -/
theorem ResizeRequest.word_length_le (r : ResizeRequest) :
    r.word.length ≤ 4 * (r.inputWidth + r.outputWidth + 1) := by
  rw [r.word_length]
  have h := bitLength_le r.outputWidth
  omega

/-- `prop:time`, paper/paper.tex: parsing the
width and streaming both copy and padding loops has linear cost. -/
theorem sourceClock_le (r : ResizeRequest) :
    sourceClock r ≤ 200 * (r.inputWidth + r.outputWidth + 1) := by
  have h := bitLength_le r.outputWidth
  unfold sourceClock bodyClock
  omega

/-- `prop:time`, paper/paper.tex: the canonical
target-width prefix creates only linear ordinary binary workspace. -/
theorem resize_setup_width_le (r : ResizeRequest) :
    resizeSizes.W (leadOnes r.word) ≤ 128 * (r.outputWidth + 1) := by
  simp only [resizeSizes, Sz.W, one_mul, input_leadOnes, natBitLength, pow_succ]
  have h := Nat.pow_log_le_add_one 2 r.outputWidth
  omega

theorem scalar_setup_bound {W L V T : ℕ} (hW : W ≤ 128 * V) (hL : L ≤ V)
    (hV : 1 ≤ V) : W + L + 64 + 1 + T + 1 ≤ (T + 300) * V := by
  nlinarith

theorem scalar_compiler_bound (A V : ℕ) (hA : 1 ≤ A) :
    10 ^ 6 * ((201 * V) * (A * V) ^ 2) + 40 * V ≤
      10 ^ 12 * A ^ 2 * V ^ 3 := by
  have hv3 : V ≤ V ^ 3 := Nat.le_self_pow (by decide) V
  have ha2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
  have hsmall : 40 * V ≤ 40 * A ^ 2 * V ^ 3 := by
    have hh : V ≤ A ^ 2 * V ^ 3 := hv3.trans (Nat.le_mul_of_pos_left _ ha2)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 40 hh
  have he : 10 ^ 6 * ((201 * V) * (A * V) ^ 2) =
      201000000 * A ^ 2 * V ^ 3 := by ring
  rw [he]
  nlinarith only [hsmall]

/-- `prop:time`, paper/paper.tex: one fixed
coefficient bounds every cold resize request, independently of its
payload value and the caller's child census. -/
noncomputable def resizeCostConstant : ℕ := 10 ^ 12 * (TSK resizeCallee + 300) ^ 2

/-- `prop:time`, paper/paper.tex: the actual
ordinary compiled field resizer has a fixed cubic cost in the source
and target widths, including initialization, framing and head reset. -/
theorem ResizeRequest.budget_polynomial (r : ResizeRequest) :
    r.budget ≤ resizeCostConstant * (r.inputWidth + r.outputWidth + 1) ^ 3 := by
  let V := r.inputWidth + r.outputWidth + 1
  let A := TSK resizeCallee + 300
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hL : leadOnes r.word ≤ V := by
    rw [input_leadOnes]
    have hh := bitLength_le r.outputWidth
    dsimp [V]
    omega
  have hW : resizeSizes.W (leadOnes r.word) ≤ 128 * V := by
    exact (resize_setup_width_le r).trans (Nat.mul_le_mul_left _ (by dsimp [V]; omega))
  have hG : Gof resizeCallee resizeSizes (leadOnes r.word) ≤ A * V := by
    simp only [Gof, Sz.Lk, Sz.Bk, resizeSizes, Nat.zero_mul, pow_zero, mul_zero, add_zero]
    change resizeSizes.W (leadOnes r.word) + leadOnes r.word + 64 + 1 +
      TSK resizeCallee + 1 ≤ A * V
    exact scalar_setup_bound hW hL hV
  have hN : sourceClock r + 1 ≤ 201 * V := by
    have hh := sourceClock_le r
    change sourceClock r ≤ 200 * V at hh
    omega
  have hi : 10 * r.word.length ≤ 40 * V := by
    have hh := Nat.mul_le_mul_left 10 r.word_length_le
    change 10 * r.word.length ≤ 10 * (4 * V) at hh
    omega
  have h := NearCubicGates.Close.CellsPack.lang_le2 resizeCallee resizeSizes r.word (sourceClock r)
  calc
    r.budget ≤ 10 ^ 6 * ((sourceClock r + 1) *
      Gof resizeCallee resizeSizes (leadOnes r.word) ^ 2) + 10 * r.word.length := h
    _ ≤ 10 ^ 6 * ((201 * V) * (A * V) ^ 2) + 40 * V :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2))) hi
    _ ≤ 10 ^ 12 * A ^ 2 * V ^ 3 := scalar_compiler_bound A V hA
    _ = resizeCostConstant * (r.inputWidth + r.outputWidth + 1) ^ 3 := rfl

/-- `prop:time`, paper/paper.tex: uniform
natural constants bound the actual field compiler for all requests. -/
theorem resizeBudget_polynomial :
    ∃ C e : ℕ, ∀ r : ResizeRequest, r.budget ≤ C * (r.inputWidth + r.outputWidth + 1) ^ e :=
  ⟨resizeCostConstant, 3, ResizeRequest.budget_polynomial⟩

end NearQuarticWires.StageResize
