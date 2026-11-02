import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.StagePrep.CeilSqrt

/-!
# The exact integer residual bound

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The square-root argument of `sec:params`, paper/paper.tex. -/
def xMaxArgument (n r tau : ℕ) : ℕ := 9 * (tau * tau) * n * r

/-- The exact argument expression of `sec:params`,
paper/paper.tex. -/
def xMaxExpression : AE :=
  mul (mul (mul (lit 9) (mul (var tauReg) (var tauReg))) (var vN)) (var rReg)

/-- The residual-bound computation of `sec:params`,
paper/paper.tex. -/
def xMaxProgram : St VV :=
  .seq (assign SQX xMaxExpression) (.seq ceilSqrtProgram (.op (.copy xMaxReg SQS)))

/-- The program of `sec:params`, paper/paper.tex, computes the canonical natural square-root bound. -/
theorem xMaxProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n r tau : ℕ) (hnv : a.env vN = n) (hrv : a.env rReg = r)
    (htv : a.env tauReg = tau) (hn : 0 < n) (hr : 0 < r) (ht : 0 < tau)
    (hW : xMaxArgument n r tau * xMaxArgument n r tau +
      xMaxArgument n r tau + 3 < 2 ^ C.Wd) :
    Hs C xMaxProgram a (20 * xMaxArgument n r tau + 120) (fun b =>
      b.env xMaxReg = Cells.ParameterArithmetic.ceilSqrt (9 * tau ^ 2 * n * r) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [SQX, SQS, SQF, SQT, SQU, xMaxReg, vJ]) := by
  have harg : xMaxArgument n r tau < 2 ^ C.Wd := by omega
  have ht2 : 0 < tau * tau := Nat.mul_pos ht ht
  have hp : 9 * (tau * tau) ≤ xMaxArgument n r tau :=
    (Nat.le_mul_of_pos_right _ hn).trans (Nat.le_mul_of_pos_right _ hr)
  have hp2 : 9 * (tau * tau) * n ≤ xMaxArgument n r tau := Nat.le_mul_of_pos_right _ hr
  have h9 : 9 < 2 ^ C.Wd := ((Nat.le_mul_of_pos_right _ ht2).trans hp).trans_lt harg
  have ht2cap : tau * tau < 2 ^ C.Wd :=
    ((Nat.le_mul_of_pos_left _ (by norm_num : 0 < 9)).trans hp).trans_lt harg
  have hpcap := hp.trans_lt harg
  have hp2cap := hp2.trans_lt harg
  unfold xMaxArgument at harg
  unfold xMaxProgram
  refine Hx.hs (Hs.then (assign_spec SQX (by decide) (by decide) xMaxExpression a
    (by unfold xMaxExpression; aevar) (by unfold xMaxExpression; aevar) hc
    (by unfold xMaxExpression; aeok [hnv, hrv, htv]))
    (fun b ⟨hbx, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbx' : b.env SQX = xMaxArgument n r tau := by
    simpa only [xMaxExpression, AE.eval, hnv, hrv, htv, xMaxArgument] using hbx
  refine Hs.then (ceilSqrtProgram_spec C b hbc _ hbx' hW)
    (fun d ⟨hdr, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  refine Hs.last (hs_copy C xMaxReg SQS d (by decide)) ?_
  rintro e rfl n3 hn3
  refine ⟨⟨?_, hdcp.trans hbcp, hdwq.trans hbwq, hdout.trans hbout,
    hdc.set _ _ (by decide), ?_⟩, ?_⟩
  · rw [DS.set_env_self, hdr]
    simp only [xMaxArgument, pow_two]
  · exact FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (FrS.weaken hdfr.toS (by decide)) (Fr.toS (Fr.set _ _ (by decide))))
  · simp only [xMaxExpression, AE.cost] at hn1
    omega

end NearQuarticWires.StagePrep
