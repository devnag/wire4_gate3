import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Gates.Dispatch.ParamsC

/-!
# The exact lifted-mask degree comparison

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The coarse candidate bound used while scanning the original
arity in `sec:params`, paper/paper.tex. -/
def primeDegreeMaximum (BN n J m X : ℕ) : ℕ :=
  (2 * (BN + 1) - 1) * (2 * J + 2) * (n - 1) + 4 * m * X

/-- The exact lifted-mask degree expression of `sec:params`,
paper/paper.tex, includes the residual-factor bill. -/
def primeBudgetExpression : AE :=
  add (mul (mul (sub (mul (lit 2) (var pE)) (lit 1))
    (add (mul (lit 2) (var pJM)) (lit 2))) (sub (var pP) (lit 1)))
    (mul (mul (lit 4) (var mReg)) (var xMaxReg))

/-- The exact degree comparison of `sec:params`,
paper/paper.tex. -/
def primeBudgetProgram : St VV :=
  .seq (assign pX8 primeBudgetExpression) (flagLe pPF pX8 pDM)

/-- The degree comparison of `sec:params`, paper/paper.tex, includes both the Newton-mask and mixed-residual
degrees for every candidate of the finite scan. -/
theorem primeBudgetProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (BN n J m X D e P : ℕ)
    (hJv : a.env pJM = J) (hmv : a.env mReg = m) (hXv : a.env xMaxReg = X)
    (hDv : a.env pDM = D) (hev : a.env pE = e) (hPv : a.env pP = P)
    (hepos : 1 ≤ e) (heb : e ≤ BN + 1) (hP : 2 ≤ P) (hPn : P ≤ n)
    (hW : primeDegreeMaximum BN n J m X + 2 * (BN + 1) +
      (2 * J + 2) + n + 4 * m + 256 < 2 ^ C.Wd) :
    Hs C primeBudgetProgram a 200 (fun b =>
      b.env pPF = bnat ((2 * e - 1) * (2 * J + 2) * (P - 1) + 4 * m * X ≤ D) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b [pX8, pPF, vJ]) := by
  have he' : 2 * e - 1 ≤ 2 * (BN + 1) - 1 := by omega
  have hp' : P - 1 ≤ n - 1 := by omega
  have hmask : (2 * e - 1) * (2 * J + 2) * (P - 1) ≤
      (2 * (BN + 1) - 1) * (2 * J + 2) * (n - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ he') hp'
  have hprefix : (2 * e - 1) * (2 * J + 2) ≤
      (2 * e - 1) * (2 * J + 2) * (P - 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2J : 2 * J ≤ 2 * J + 2 := by omega
  have hactual : (2 * e - 1) * (2 * J + 2) * (P - 1) + 4 * m * X ≤
      primeDegreeMaximum BN n J m X := Nat.add_le_add_right hmask _
  have hmaskCap : (2 * e - 1) * (2 * J + 2) * (P - 1) < 2 ^ C.Wd := by omega
  have hresCap : 4 * m * X < 2 ^ C.Wd := by omega
  have hsumCap : (2 * e - 1) * (2 * J + 2) * (P - 1) + 4 * m * X < 2 ^ C.Wd := by omega
  unfold primeBudgetProgram
  refine Hx.hs (Hs.then (assign_spec pX8 (by decide) (by decide) primeBudgetExpression a
    (by unfold primeBudgetExpression; aevar) (by unfold primeBudgetExpression; aevar) hc
    (by unfold primeBudgetExpression; aeok [hJv, hmv, hXv, hev, hPv]))
    (fun b ⟨hbx, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbx' : b.env pX8 = (2 * e - 1) * (2 * J + 2) * (P - 1) + 4 * m * X := by
    simpa only [primeBudgetExpression, AE.eval, hJv, hmv, hXv, hev, hPv] using hbx
  have hbD : b.env pDM = D := (hbfr _ (by decide) (by decide) (by decide)).trans hDv
  refine Hs.last (flagLe_spec pPF pX8 pDM (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) b hbc (by omega))
    (fun d ⟨hdf, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  refine ⟨⟨?_, hdcp.trans hbcp, hdwq.trans hbwq, hdout.trans hbout, hdc,
    FrS.trans (hbfr.toS _ (by decide) (by decide)) (hdfr.toS _ (by decide) (by decide))⟩, ?_⟩
  · rw [hdf, hbx', hbD]
  · simp only [primeBudgetExpression, AE.cost] at hn1
    omega

end NearQuarticWires.StagePrep
