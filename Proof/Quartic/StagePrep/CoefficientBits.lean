import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# The exact coefficient-height bound

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The coefficient-height computation of `sec:params`,
paper/paper.tex, uses a binary ceiling logarithm. -/
def coefficientBitsProgram : St VV :=
  .seq (assign t3 (mul (mul (var nSideReg) (var nSideReg)) (var qReg)))
    (.seq clog2 (assign coefficientBitsReg
      (add (add (add (var seedLengthReg) (mul (var mReg) (var pK)))
        (mul (mul (lit 2) (var mReg)) (var t5))) (lit 1))))

/-- The height bound of `sec:params`, paper/paper.tex, is computed exactly from the actual sample and seed
sizes, without enumerating either one. -/
theorem coefficientBitsProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (N Q S m k : ℕ) (hNv : a.env nSideReg = N) (hQv : a.env qReg = Q)
    (hSv : a.env seedLengthReg = S) (hmv : a.env mReg = m) (hkv : a.env pK = k)
    (hQ : 0 < Q)
    (hW : 2 * N * N * Q + S + m * k +
      2 * m * Nat.clog 2 (N * N * Q) + 2 * m + 32 < 2 ^ C.Wd) :
    Hs C coefficientBitsProgram a (5 * Nat.clog 2 (N * N * Q) + 100) (fun b =>
      b.env coefficientBitsReg = S + m * k + 2 * m * Nat.clog 2 (N ^ 2 * Q) + 1 ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [t3, t5, t6, coefficientBitsReg, vJ]) := by
  have hNN : N * N ≤ N * N * Q := Nat.le_mul_of_pos_right _ hQ
  have htwo : 2 * (N * N * Q) = 2 * N * N * Q := by ring
  unfold coefficientBitsProgram
  refine Hx.hs (Hs.then (assign_spec t3 (by decide) (by decide)
    (.mul (.mul (.var nSideReg) (.var nSideReg)) (.var qReg)) a
    (by aevar) (by aevar) hc (by aeok [hNv, hQv, htwo]))
    (fun b ⟨hbx, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbx' : b.env t3 = N * N * Q := by simpa only [AE.eval, hNv, hQv] using hbx
  refine Hs.then (clog2_spec b hbc (by rw [hbx', htwo]; omega))
    (fun d ⟨hdl, _, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdl' : d.env t5 = Nat.clog 2 (N * N * Q) := by simpa only [hbx'] using hdl
  have hdS : d.env seedLengthReg = S := by
    rw [hdfr _ (by decide), hbfr _ (by decide) (by decide) (by decide), hSv]
  have hdm : d.env mReg = m := by
    rw [hdfr _ (by decide), hbfr _ (by decide) (by decide) (by decide), hmv]
  have hdk : d.env pK = k := by
    rw [hdfr _ (by decide), hbfr _ (by decide) (by decide) (by decide), hkv]
  refine Hs.last (assign_spec coefficientBitsReg (by decide) (by decide)
    (.add (.add (.add (.var seedLengthReg) (.mul (.var mReg) (.var pK)))
      (.mul (.mul (.lit 2) (.var mReg)) (.var t5))) (.lit 1)) d
    (by aevar) (by aevar) hdc (by aeok [hdS, hdm, hdk, hdl']))
    (fun e ⟨heb, hefr, hecp, hewq, heout, hec⟩ n3 hn3 => ?_)
  refine ⟨⟨?_, hecp.trans (hdcp.trans hbcp), hewq.trans (hdwq.trans hbwq),
    heout.trans (hdout.trans hbout), hec, ?_⟩, ?_⟩
  · simpa only [AE.eval, hdS, hdm, hdk, hdl', pow_two] using heb
  · exact FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (FrS.weaken hdfr.toS (by decide)) (hefr.toS _ (by decide) (by decide)))
  · simp only [AE.cost] at hn1 hn3
    have hn2' : n2 ≤ 5 * Nat.clog 2 (N * N * Q) + 6 := by simpa only [hbx'] using hn2
    omega

end NearQuarticWires.StagePrep
