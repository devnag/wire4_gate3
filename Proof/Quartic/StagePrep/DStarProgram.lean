import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Gates.Dispatch.ParamsB

/-!
# The exact incidence-cutoff quotient

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The integer quotient for `dstar` in `sec:params`,
paper/paper.tex. -/
def dStarProgram : St VV := assign dStarReg
  (div (mul (mul (lit 2) (var xMaxReg)) (var pU))
    (mul (mul (lit 3) (var rReg)) (var tauReg)))

/-- The cutoff computation of `sec:params`, paper/paper.tex, is the exact natural quotient in37steps. -/
theorem dStarProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (X U r tau : ℕ) (hXv : a.env xMaxReg = X) (hUv : a.env pU = U)
    (hrv : a.env rReg = r) (htv : a.env tauReg = tau)
    (hU : 0 < U) (hr : 0 < r) (ht : 0 < tau)
    (hW : 2 * X * U + 6 * r * tau + 16 < 2 ^ C.Wd) :
    Hs C dStarProgram a 37 (fun b => b.env dStarReg = 2 * X * U / (3 * r * tau) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b [dStarReg, vJ]) := by
  have hnum : 2 * X ≤ 2 * X * U := Nat.le_mul_of_pos_right _ hU
  have hden : 3 * r ≤ 3 * r * tau := Nat.le_mul_of_pos_right _ ht
  have hdenpos : 0 < 3 * r * tau := Nat.mul_pos (Nat.mul_pos (by norm_num) hr) ht
  have hden2 : 2 * (3 * r * tau) = 6 * r * tau := by ring
  unfold dStarProgram
  refine Hs.mono (assign_spec dStarReg (by decide) (by decide)
    (.div (.mul (.mul (.lit 2) (.var xMaxReg)) (.var pU))
      (.mul (.mul (.lit 3) (.var rReg)) (.var tauReg))) a
    (by aevar) (by aevar) hc (by aeok [hXv, hUv, hrv, htv, hden2])) le_rfl ?_
  rintro b ⟨hb, hfr, hcp, hwq, hout, hbc⟩
  exact ⟨by simpa only [AE.eval, hXv, hUv, hrv, htv] using hb,
    hcp, hwq, hout, hbc, hfr.toS _ (by decide) (by decide)⟩

end NearQuarticWires.StagePrep
