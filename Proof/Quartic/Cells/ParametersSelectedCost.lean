import Proof.Quartic.Cells.ParametersPublicCost
import Proof.Quartic.Cells.ParametersAttemptWidths
import Proof.Quartic.StagePrep.SelectedDriver

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: the exact complete guarded execution charge is
polynomial in the original input length, including every possible
rejected search, without using any final rate-chain success. -/
theorem selectedPreparationCost_preparation_bound (hs : CoreRules x p) (B1 L num den : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den)
    (hnumBits : num ≤ 2 ^ L) (hdenBits : den ≤ 2 ^ L)
    (hP : p.P ≤ x.n) (hD : p.Dprime ≤ (x.n + 1) ^ 2) (hh : p.h ≤ x.n) :
    StagePrep.selectedPreparationCost x p num den ≤
      (publicScalesCostCoefficient B1 + 100000 * (32 * B1 + 2203) ^ 4 +
        10 * (preparationCoefficient B1 + 33 * B1 + 4000)) *
        (L + 1) ^ (2 * B1 + 12) := by
  let u := L + 1
  let V := (32 * B1 + 2203) * u ^ 2
  let H := preparationBitBase B1 L
  let R := (L + 1) ^ (2 * B1 + 12)
  have hu1 : 1 ≤ u := Nat.succ_pos L
  have hu2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ hu1
  have huu2 : u ≤ u ^ 2 := Nat.le_self_pow (by norm_num) _
  have hVu2 : u ^ 2 ≤ V := Nat.le_mul_of_pos_left _ (by omega)
  have hV1 : 1 ≤ V := hu2.trans hVu2
  have hnV : x.n ≤ V := (hn.trans (Nat.le_succ L)).trans (huu2.trans hVu2)
  have hPV : p.P ≤ V := hP.trans hnV
  have hhV : p.h ≤ V := hh.trans hnV
  have hDV : p.Dprime ≤ V := hD.trans
    ((Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2).trans hVu2)
  have hBN := hs.BN_preparation_bound B1 hb
  have hn2 : x.n ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left (hn.trans (Nat.le_succ L)) _
  have hBNV : p.BN - 1 + 3 ≤ V := by dsimp only [V]; nlinarith only [hBN, hn2, hu2, Nat.sub_le p.BN 1]
  have hJV : Jmax x.n ≤ V := by
    have heq : Jmax x.n = p.Jmax := by rw [hs.Jmax_eq, hs.mu_eq]; rfl
    rw [heq, hs.Jmax_eq]
    exact (Nat.add_le_add_right (hs.mu_le_lambda.trans hs.lambda_le_n) 1).trans
      ((Nat.add_le_add_right hn 1).trans (huu2.trans hVu2))
  have hprint := hs.printing_operand_binary_bounds B1 L hn hb
  have hlogU : Nat.clog 2 p.Uocc ≤ H := hprint.2.2.2.2.2.2.2.2.1
  have hlogN : Nat.clog 2 (p.N * p.N * p.Q) ≤ H := hprint.2.2.2.2.2.2.2.2.2
  have h1V4 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ hV1
  have hVV4 : V ≤ V ^ 4 := Nat.le_self_pow (by norm_num) _
  have hV2V4 : V ^ 2 ≤ V ^ 4 := Nat.pow_le_pow_right hV1 (by norm_num)
  have hV3V4 : V ^ 3 ≤ V ^ 4 := Nat.pow_le_pow_right hV1 (by norm_num)
  have hLift : liftCost (p.BN - 1) ≤ 70 * V ^ 2 + 200 := by
    unfold liftCost
    have hm := Nat.mul_le_mul hBNV hBNV
    nlinarith only [hm]
  have hSearch : StagePrep.primeSearchCost p.BN x.n ≤ 5000 * V ^ 4 := by
    have hn4 : x.n + 4 ≤ 5 * V := by omega
    calc
      StagePrep.primeSearchCost p.BN x.n ≤ (5 * V) * (70 * V ^ 2 + 720) + 100 := by
        unfold StagePrep.primeSearchCost
        exact Nat.add_le_add_right (Nat.mul_le_mul hn4 (by omega)) _
      _ ≤ _ := by nlinarith only [hVV4, hV3V4, h1V4]
  have hPrimes : primesCost p.P ≤ 500 * V ^ 4 := by
    calc
      primesCost p.P ≤ (V + 1) * (9 * V + 100 + 2) + 100 := by unfold primesCost; gcongr
      _ ≤ _ := by nlinarith only [hVV4, hV2V4, h1V4]
  have hPair : pairCost p.Dprime ≤ 1000 * V ^ 4 := by
    calc
      pairCost p.Dprime ≤ (V + 2) * (V * (V * (28 * V + 30) + 30) + 100 + 10) + 20 := by
        unfold pairCost aCost
        gcongr
      _ ≤ _ := by nlinarith only [hVV4, hV2V4, hV3V4, h1V4]
  have hChain : chainCost (Jmax x.n) p.h ≤ 9000 * V ^ 4 := by
    calc
      chainCost (Jmax x.n) p.h ≤ (V + 1) * (60 * V + 3000 + 2) + 2000 := by
        unfold chainCost bodyCost
        gcongr
      _ ≤ _ := by nlinarith only [hVV4, hV2V4, h1V4]
  have hTail : StagePrep.selectedPreparationCost x p num den ≤
      StagePrep.publicScalesCost x p num den + 100000 * V ^ 4 + 10 * H := by
    unfold StagePrep.selectedPreparationCost
    nlinarith only [hSearch, hLift, hPrimes, hPair, hChain, hlogU, hlogN,
      hnV, hVV4, hV2V4, h1V4]
  have h8 : u ^ 8 ≤ R := Nat.pow_le_pow_right hu1 (by omega)
  have hV4 : V ^ 4 ≤ (32 * B1 + 2203) ^ 4 * R := by
    calc
      V ^ 4 = (32 * B1 + 2203) ^ 4 * u ^ 8 := by dsimp only [V]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ h8
  have hHR : H ≤ (preparationCoefficient B1 + 33 * B1 + 4000) * R :=
    (preparationBitBase_cubic B1 L).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right hu1 (by omega)))
  have hPublic := hs.publicScalesCost_preparation_bound B1 L num den hn hb
    hnum hden hu hd hnumBits hdenBits
  change StagePrep.publicScalesCost x p num den ≤ publicScalesCostCoefficient B1 * R at hPublic
  calc
    StagePrep.selectedPreparationCost x p num den ≤
        publicScalesCostCoefficient B1 * R +
          100000 * ((32 * B1 + 2203) ^ 4 * R) +
          10 * ((preparationCoefficient B1 + 33 * B1 + 4000) * R) := by omega
    _ = _ := by dsimp only [R]; ring

end NearQuarticWires.Cells.CoreRules
