import Proof.Quartic.StageMainPopulation.Machine
import Proof.Quartic.StageMainPopulation.Clock

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicGates.Close.Dispatch
open StageMainMask

/-- `prop:time`, paper/paper.tex: the complete
ordinary arithmetic budget pays binary width, both original bank scans,
physical witness addressing and every cold setup and output operation. -/
theorem populationArithmeticBudget_le (r : PopulationRequest) :
    populationArithmeticBudget r ≤ 1000000000 * (r.word.length + 5)^12 := by
  let L := r.word.length
  change populationArithmeticBudget r ≤ 1000000000 * (L + 5)^12
  let N := 3 * rawSteps r L + 2
  have ht := rawSteps_le r
  have hp24 : (L + 2)^4 ≤ (L + 5)^4 := Nat.pow_le_pow_left (by omega) 4
  have hp04 : 1 ≤ (L + 5)^4 := Nat.one_le_pow _ _ (by omega)
  have hN : N ≤ 30002 * (L + 5)^4 := by
    have h := Nat.mul_le_mul_left 10000 hp24
    dsimp [N, L] at *
    omega
  have hW : wdOf 4 L + 1 ≤ 2 * (L + 5)^4 := by
    have h := Nat.pow_le_pow_left (show L + 4 ≤ L + 5 by omega) 4
    dsimp [wdOf]
    omega
  have hKC : KC (wdOf 4 L) ≤ 2000 * (L + 5)^8 := by
    unfold KC
    calc
      _ ≤ 500 * (2 * (L + 5)^4)^2 :=
        Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hW 2)
      _ = _ := by ring
  have hproduct : N * KC (wdOf 4 L) ≤ 60004000 * (L + 5)^12 := by
    calc
      _ ≤ (30002 * (L + 5)^4) * (2000 * (L + 5)^8) := Nat.mul_le_mul hN hKC
      _ = _ := by ring
  have hsetup : setupCost VV 4 L ≤ 100000 * (L + 5)^4 := by
    unfold setupCost
    rw [show L + 4 + 1 = L + 5 by omega]
    exact Nat.mul_le_mul_right _ (by decide : 200 * (VV + 2) ≤ 100000)
  have hp4 : (L + 5)^4 ≤ (L + 5)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp0 : 1 ≤ (L + 5)^12 := Nat.one_le_pow _ _ (by omega)
  have hp1 : L ≤ (L + 5)^12 := by
    have h : L + 5 ≤ (L + 5)^12 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < L + 5) (by decide : 1 ≤ 12)
    omega
  have hs := hsetup.trans (Nat.mul_le_mul_left 100000 hp4)
  have hn := hN.trans (Nat.mul_le_mul_left 30002 hp4)
  change setupCost VV 4 L + N * KC (wdOf 4 L) + 30 * N + 50 * L + 300 ≤ _
  omega

/-- `prop:time`, paper/paper.tex: actual source
framing, the complete ordinary machine and physical handoff are all
bounded by one fixed polynomial in the literal request length. -/
theorem populationBudget_fixed (r : PopulationRequest) :
    populationBudget r ≤ (5000000000 * 5^12) * (r.word.length + 1)^12 := by
  let L := r.word.length
  have ha := populationArithmeticBudget_le r
  change populationArithmeticBudget r ≤ 1000000000 * (L + 5)^12 at ha
  have hp0 : 1 ≤ (L + 5)^12 := Nat.one_le_pow _ _ (by omega)
  have hp1 : L + 1 ≤ (L + 5)^12 := by
    have h : L + 5 ≤ (L + 5)^12 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < L + 5) (by decide : 1 ≤ 12)
    omega
  have hraw : populationBudget r ≤ 5000000000 * (L + 5)^12 := by
    unfold populationBudget
    change 1600 * (L + 1) + 4 * populationArithmeticBudget r + 12 ≤ _
    omega
  have hscale : (L + 5)^12 ≤ (5 * (L + 1))^12 := Nat.pow_le_pow_left (by omega) 12
  calc
    _ ≤ 5000000000 * (L + 5)^12 := hraw
    _ ≤ 5000000000 * (5 * (L + 1))^12 := Nat.mul_le_mul_left _ hscale
    _ = _ := by rw [mul_pow]; ring

/-- `prop:time`, paper/paper.tex: the physical
cold population procedure has uniform natural polynomial constants and
requires no initialized source, parser, callee, width or provider premise. -/
theorem populationBudget_polynomial :
    ∃ K d : ℕ, ∀ r : PopulationRequest, populationBudget r ≤ K * (r.word.length + 1)^d :=
  ⟨5000000000 * 5^12, 12, populationBudget_fixed⟩

end NearQuarticWires.StageMainPopulation
