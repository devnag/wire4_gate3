import Proof.Quartic.StageMainMask.StructuralMachine
import Proof.Quartic.StageCert.StructuralCost

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicGates.Close.Dispatch

/-- `prop:time`, paper/paper.tex: the complete
original-call traversal, binary field parsing and structural scans
have polynomial cost in their actual finite source length. -/
theorem structuralRawSteps_le (r : StructuralRawRequest) :
    structuralRawSteps r r.word.length ≤ 5000 * (r.word.length + 2) ^ 4 := by
  let L := r.word.length
  change structuralRawSteps r L ≤ 5000 * (L + 2) ^ 4
  have hr : r.partition.r ≤ L := r.geometry_bounds.2.2.trans r.encoding_bounds.1
  have hlen : ((structuralFields r.partition r.threshold r.left r.right).flatMap
      (fun f => NearCubicWires.RepairRepresentation.natWord f.2)).length ≤ L := by
    simp [L, StructuralRawRequest.word]
  have hread : StageOutput.readScalarsCost
      (structuralFields r.partition r.threshold r.left r.right) ≤ 40 * L + 1 :=
    (StageOutput.readScalarsCost_le_word _).trans (by omega)
  have hs := StageCert.structural_steps_le L r.partition.r L hr
  have hscan : 2 * (r.partition.r / 2) * (1204 * (L + 2) ^ 3 + 2) ≤
      1246 * (L + 2) ^ 4 := by
    calc
      _ ≤ 2 * (r.partition.r / 2) * (1204 * (L + 2) ^ 3 + 2) + 40 := by omega
      _ ≤ 1246 * (L + 1) * (L + 2) ^ 3 := hs
      _ ≤ 1246 * (L + 2) * (L + 2) ^ 3 := by gcongr; omega
      _ = _ := by ring
  have hp3 : (L + 2) ^ 3 ≤ (L + 2) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : L ≤ (L + 2) ^ 4 := by
    have h : L + 2 ≤ (L + 2) ^ 4 := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (by omega : 0 < L + 2) (by decide : 1 ≤ 4)
    omega
  have hp0 : 1 ≤ (L + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hcall := Nat.mul_le_mul_left 3000 hp3
  change 3000 * (L + 2) ^ 3 + _ + _ + 80 ≤ _
  omega

/-- `prop:time`, paper/paper.tex: the full
ordinary structural arithmetic budget includes the compiler's binary
width overhead without dependence on the scalar code values. -/
theorem structuralArithmeticBudget_le (r : StructuralRawRequest) :
    structuralArithmeticBudget r ≤ 1000000000 * (r.word.length + 5) ^ 12 := by
  let L := r.word.length
  change structuralArithmeticBudget r ≤ 1000000000 * (L + 5) ^ 12
  let N := 3 * structuralRawSteps r L + 2
  have ht := structuralRawSteps_le r
  have hp24 : (L + 2) ^ 4 ≤ (L + 5) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hp04 : 1 ≤ (L + 5) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hN : N ≤ 15002 * (L + 5) ^ 4 := by
    have h := Nat.mul_le_mul_left 5000 hp24
    dsimp [N, L] at *
    omega
  have hW : wdOf 4 L + 1 ≤ 2 * (L + 5) ^ 4 := by
    have h := Nat.pow_le_pow_left (show L + 4 ≤ L + 5 by omega) 4
    dsimp [wdOf]
    omega
  have hKC : KC (wdOf 4 L) ≤ 2000 * (L + 5) ^ 8 := by
    unfold KC
    calc
      _ ≤ 500 * (2 * (L + 5) ^ 4) ^ 2 :=
        Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hW 2)
      _ = _ := by ring
  have hproduct : N * KC (wdOf 4 L) ≤ 30004000 * (L + 5) ^ 12 := by
    calc
      _ ≤ (15002 * (L + 5) ^ 4) * (2000 * (L + 5) ^ 8) := Nat.mul_le_mul hN hKC
      _ = _ := by ring
  have hsetup : setupCost VV 4 L ≤ 100000 * (L + 5) ^ 4 := by
    unfold setupCost
    rw [show L + 4 + 1 = L + 5 by omega]
    exact Nat.mul_le_mul_right _ (by decide : 200 * (VV + 2) ≤ 100000)
  have hp4 : (L + 5) ^ 4 ≤ (L + 5) ^ 12 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp0 : 1 ≤ (L + 5) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hp1 : L ≤ (L + 5) ^ 12 := by
    have h : L + 5 ≤ (L + 5) ^ 12 := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (by omega : 0 < L + 5) (by decide : 1 ≤ 12)
    omega
  have hs := hsetup.trans (Nat.mul_le_mul_left 100000 hp4)
  have hn := hN.trans (Nat.mul_le_mul_left 15002 hp4)
  change setupCost VV 4 L + N * KC (wdOf 4 L) + 30 * N + 50 * L + 300 ≤ _
  omega

/-- `prop:time`, paper/paper.tex: the cold
structural source machine's framing and compiled execution admit a
fixed polynomial in the actual finite input word length. -/
theorem structuralRawBudget_polynomial :
    ∃ K : ℕ, ∀ r : StructuralRawRequest,
      structuralRawBudget r ≤ K * (r.word.length + 1) ^ 12 := by
  refine ⟨5000000000 * 5 ^ 12, ?_⟩
  intro r
  let L := r.word.length
  have ha := structuralArithmeticBudget_le r
  change structuralArithmeticBudget r ≤ 1000000000 * (L + 5) ^ 12 at ha
  have hp0 : 1 ≤ (L + 5) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hp1 : L + 1 ≤ (L + 5) ^ 12 := by
    have h : L + 5 ≤ (L + 5) ^ 12 := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (by omega : 0 < L + 5) (by decide : 1 ≤ 12)
    omega
  have hraw : structuralRawBudget r ≤ 5000000000 * (L + 5) ^ 12 := by
    unfold structuralRawBudget
    change 1600 * (L + 1) + 4 * structuralArithmeticBudget r + 12 ≤ _
    omega
  have hscale : (L + 5) ^ 12 ≤ (5 * (L + 1)) ^ 12 :=
    Nat.pow_le_pow_left (by omega) 12
  calc
    _ ≤ 5000000000 * (L + 5) ^ 12 := hraw
    _ ≤ 5000000000 * (5 * (L + 1)) ^ 12 := Nat.mul_le_mul_left _ hscale
    _ = _ := by rw [mul_pow]; ring

end NearQuarticWires.StageMainMask
