import Proof.Quartic.Cells.ParametersGammaRuntimeScales

set_option autoImplicit false

namespace NearQuarticWires.Cells

open StageGamma
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the ordinary compiler
is linear in the number of source steps, so its complete physical charge
retains the original eighth-power choice census. -/
theorem gamma_compiled_cost_bound (request : Machine.GammaRequest) :
    let q := Cycle.seedLength request.parameters + 9
    compiledGammaCost request ≤
      (10 ^ 72 * (TSK compactGaussCallee + 1) ^ 2) *
        ((request.parameters.Q + 1) ^ 8 * q ^ 24) := by
  let q := Cycle.seedLength request.parameters + 9
  let E := (request.parameters.Q + 1) ^ 8
  let T := TSK compactGaussCallee
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hq12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ hq
  have hE12 : 1 ≤ E * q ^ 12 := by nlinarith only [hE, hq12]
  have hN := gamma_compiled_source_bound request
  change compiledGammaSourceCost request ≤ 10 ^ 26 * E * q ^ 12 at hN
  have hN1 : compiledGammaSourceCost request + 1 ≤ 10 ^ 27 * E * q ^ 12 := by
    norm_num at hN ⊢
    nlinarith only [hN, hE12]
  have hG := gamma_compiler_constant_bound request
  change NearCubicGates.Close.CellsPack.Gof compactGaussCallee gammaSizes _ ≤
    10 ^ 18 * (T + 1) * q ^ 6 at hG
  have hi := (gamma_runtime_scales request).2.2.2.2
  change (cachedRequestWord request).length ≤ 43 * q at hi
  have hq24 : q ≤ q ^ 24 := Nat.le_self_pow (by norm_num) q
  have hE24 : q ^ 24 ≤ E * q ^ 24 := Nat.le_mul_of_pos_left _ (by omega)
  have hT24 : E * q ^ 24 ≤ (T + 1) ^ 2 * (E * q ^ 24) :=
    Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos T))
  have hsmall : q ≤ (T + 1) ^ 2 * (E * q ^ 24) := hq24.trans (hE24.trans hT24)
  calc
    compiledGammaCost request ≤
        10 ^ 6 * ((compiledGammaSourceCost request + 1) *
          NearCubicGates.Close.CellsPack.Gof compactGaussCallee gammaSizes
            (NearCubicGates.Close.Cells.leadOnes (cachedRequestWord request)) ^ 2) +
          10 * (cachedRequestWord request).length :=
      NearCubicGates.Close.CellsPack.lang_le2 _ _ _ _
    _ ≤ 10 ^ 6 * ((10 ^ 27 * E * q ^ 12) *
          (10 ^ 18 * (T + 1) * q ^ 6) ^ 2) + 10 * (43 * q) := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul hN1 (Nat.pow_le_pow_left hG _)))
        (Nat.mul_le_mul_left _ hi)
    _ = 10 ^ 69 * ((T + 1) ^ 2 * (E * q ^ 24)) + 430 * q := by ring
    _ ≤ (10 ^ 72 * (T + 1) ^ 2) * (E * q ^ 24) := by
      norm_num
      nlinarith only [hsmall]

end NearQuarticWires.Cells
