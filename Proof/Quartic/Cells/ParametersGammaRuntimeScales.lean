import Proof.Quartic.StageGamma.Compiled
import Proof.Quartic.StageGamma.CachedBudget
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false

namespace NearQuarticWires.Cells

open StageGamma
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary_length)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.PrefixProg

/-- `prop:time`, paper/paper.tex: the actual
compiler widths, reset reserves and retained input are polynomial
in the original seed length, independently of the choice census. -/
theorem gamma_runtime_scales (request : Machine.GammaRequest) :
    let q := Cycle.seedLength request.parameters + 9
    let L := leadOnes (cachedRequestWord request)
    gammaSizes.W L ≤ 512 * q ∧ gammaSizes.Lk L ≤ 2000000 * q ∧
      gammaSizes.Bk L ≤ (64 * 10 ^ 15) * q ^ 6 ∧ L ≤ q ∧
      (cachedRequestWord request).length ≤ 43 * q := by
  let S := Cycle.seedLength request.parameters
  have hell : request.parameters.ell ≤ S := by dsimp [S, Cycle.seedLength]; omega
  have hpow : 2 ^ natBitLength request.parameters.ell ≤ 2 * (S + 9) :=
    (pow_nbl_le _).trans (by omega)
  have hL : natBitLength request.parameters.ell ≤ S + 9 :=
    (nbl_le_self' _).trans (by omega)
  have hinput := gammaRequestWord_length_le request
  have hcached : (cachedRequestWord request).length ≤ 43 * (S + 9) := by
    simp only [cachedRequestWord, List.length_append, binary_length]
    omega
  rw [cachedRequest_leadOnes]
  refine ⟨?_, ?_, ?_, hL, hcached⟩
  · dsimp [gammaSizes, Sz.W]
    simp only [one_mul]
    nlinarith only [hpow]
  · dsimp [gammaSizes, Sz.Lk]
    simp only [one_mul]
    nlinarith only [hpow]
  · dsimp [gammaSizes, Sz.Bk]
    rw [show 6 * natBitLength request.parameters.ell = natBitLength request.parameters.ell * 6 by omega,
      pow_mul]
    calc
      _ ≤ (2 * (S + 9)) ^ 6 * 10 ^ 15 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpow _)
      _ = _ := by ring

/-- `prop:time`, paper/paper.tex: the exact source
program pays its true eighth-power choice loop and only a fixed
sixth-power seed factor for all remaining operations. -/
theorem gamma_source_body_bound (request : Machine.GammaRequest) :
    let q := Cycle.seedLength request.parameters + 9
    let L := leadOnes (cachedRequestWord request)
    gammaCachedBodyCost request (gammaSizes.W L) ≤
      10 ^ 8 * (request.parameters.Q + 1) ^ 8 * q ^ 6 := by
  let q := Cycle.seedLength request.parameters + 9
  let E := (request.parameters.Q + 1) ^ 8
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hq6 : q ≤ q ^ 6 := Nat.le_self_pow (by norm_num) q
  have h1q6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hEq : q ^ 6 ≤ E * q ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have hqEq : q ≤ E * q ^ 6 := hq6.trans hEq
  have hEEq : E ≤ E * q ^ 6 := Nat.le_mul_of_pos_right _ (by omega)
  have h1Eq : 1 ≤ E * q ^ 6 := h1q6.trans hEq
  have hW := (gamma_runtime_scales request).1
  change gammaSizes.W (leadOnes (cachedRequestWord request)) ≤ 512 * q at hW
  change 600 * q + (E * (2000010 * q ^ 6 + 8) + 4) +
    40 * gammaSizes.W (leadOnes (cachedRequestWord request)) + 136 ≤ 10 ^ 8 * E * q ^ 6
  norm_num
  nlinarith only [hW, hqEq, hEEq, h1Eq]

/-- `prop:time`, paper/paper.tex: enlarging the
Gaussian reset and work reserves multiplies the actual source charge
by only a sixth-power seed factor. -/
theorem gamma_compiled_source_bound (request : Machine.GammaRequest) :
    let q := Cycle.seedLength request.parameters + 9
    compiledGammaSourceCost request ≤ 10 ^ 26 * (request.parameters.Q + 1) ^ 8 * q ^ 12 := by
  let q := Cycle.seedLength request.parameters + 9
  let L := leadOnes (cachedRequestWord request)
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hq6 : q ≤ q ^ 6 := Nat.le_self_pow (by norm_num) q
  have h1q6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have hLk : gammaSizes.Lk L ≤ 2000000 * q := (gamma_runtime_scales request).2.1
  have hBk : gammaSizes.Bk L ≤ (64 * 10 ^ 15) * q ^ 6 := (gamma_runtime_scales request).2.2.1
  have hreserve : 1 + gammaSizes.Lk L + gammaSizes.Bk L ≤ 10 ^ 18 * q ^ 6 := by
    norm_num at hBk ⊢
    nlinarith only [hLk, hBk, hq6, h1q6]
  calc
    compiledGammaSourceCost request ≤
        (10 ^ 8 * (request.parameters.Q + 1) ^ 8 * q ^ 6) * (10 ^ 18 * q ^ 6) :=
      Nat.mul_le_mul (gamma_source_body_bound request) hreserve
    _ = _ := by ring

/-- `prop:time`, paper/paper.tex: the compiler's
constant overhead depends on the seed scale and fixed Gaussian
machine description, and does not contain the choice census. -/
theorem gamma_compiler_constant_bound (request : Machine.GammaRequest) :
    let q := Cycle.seedLength request.parameters + 9
    NearCubicGates.Close.CellsPack.Gof compactGaussCallee gammaSizes
      (leadOnes (cachedRequestWord request)) ≤
        10 ^ 18 * (TSK compactGaussCallee + 1) * q ^ 6 := by
  let q := Cycle.seedLength request.parameters + 9
  let L := leadOnes (cachedRequestWord request)
  let T := TSK compactGaussCallee
  have hs := gamma_runtime_scales request
  change gammaSizes.W L ≤ 512 * q ∧ gammaSizes.Lk L ≤ 2000000 * q ∧
    gammaSizes.Bk L ≤ (64 * 10 ^ 15) * q ^ 6 ∧ L ≤ q ∧ _ at hs
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hq6 : q ≤ q ^ 6 := Nat.le_self_pow (by norm_num) q
  have h1q6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have hTK : q ^ 6 ≤ (T + 1) * q ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have hTTK : T ≤ (T + 1) * q ^ 6 := by nlinarith only [h1q6]
  have hqTK : q ≤ (T + 1) * q ^ 6 := hq6.trans hTK
  have h1TK : 1 ≤ (T + 1) * q ^ 6 := h1q6.trans hTK
  dsimp only [NearCubicGates.Close.CellsPack.Gof]
  change gammaSizes.W L + gammaSizes.Lk L + gammaSizes.Bk L + L +
    256 + 1000000 + 10 ^ 15 + 1 + 1 + 6 + T + 1 ≤ 10 ^ 18 * (T + 1) * q ^ 6
  have hW := hs.1
  have hLk := hs.2.1
  have hBk := hs.2.2.1
  have hL := hs.2.2.2.1
  norm_num at hBk ⊢
  nlinarith only [hW, hLk, hBk, hL, hqTK, hTK, hTTK, h1TK]

end NearQuarticWires.Cells
