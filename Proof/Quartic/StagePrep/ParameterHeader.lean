import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.StagePrep.IntegerCensus

/-!
# The logarithmic parameters and fixed interaction order

Paper: `sec:params`, paper/paper.tex, and
`prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates
open AE

/-- The first scalars of `sec:params`, paper/paper.tex, with the actual wire census as public size. -/
def parameterHeader : St VV :=
  .seq (pHdr 0) (.seq (assign mReg (lit 4))
    (.seq (assign rReg (mul (lit 16) (var pMU))) (.op (.copy pW censusTotal))))

/-- The registers changed by `sec:params`, paper/paper.tex. -/
def parameterHeaderT : List (Fin VV) := mReg :: rReg :: hdrT

/-- The computation of `sec:params`, paper/paper.tex, produces the exact logarithms, `m=4`, `r=16*mu`,
and actual wire count. -/
theorem parameterHeader_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n w1 w2 : ℕ) (hn : a.env vN = n)
    (hw1 : a.env vTW1 = w1) (hw2 : a.env vTW2 = w2)
    (hW : (3 * n + 4) * (n + 1) + w1 + w2 + 34 * n + 36 < 2 ^ C.Wd) :
    Hs C parameterHeader a (20 * n + 180) (fun b =>
      b.env pLAM = Target.lambda n ∧ b.env pMU = Target.mu n ∧
      b.env pJM = Target.mu n + 1 ∧ b.env mReg = 4 ∧
      b.env rReg = 16 * Target.mu n ∧ b.env pW = a.env censusTotal ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ FrS a b parameterHeaderT) := by
  have hmu : Target.mu n ≤ n := (clog_le_self _).trans (clog_le_self n)
  have hbase : (3 * n + 0 + 4) * (n + 1) + w1 + w2 + 2 * n + 4 < 2 ^ C.Wd := by
    simp only [Nat.add_zero]
    omega
  unfold parameterHeader
  refine Hx.hs (Hs.then (pHdr_spec 0 a hc n w1 w2 hn hw1 hw2 hbase)
    (fun b ⟨hbl, hbm, hbj, _, _, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  refine Hs.then (assign_spec mReg (by decide) (by decide) (.lit 4) b
    (by aevar) (by aevar) hbc (by aeok []))
    (fun d ⟨hdm, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hdmu : d.env pMU = Target.mu n := by
    rw [hdfr _ (by decide) (by decide) (by decide), hbm]
  refine Hs.then (assign_spec rReg (by decide) (by decide)
    (.mul (.lit 16) (.var pMU)) d (by aevar) (by aevar) hdc
    (by aeok [hdmu]))
    (fun e ⟨her, hefr, hecp, hewq, heout, hec⟩ n3 hn3 => ?_)
  refine Hs.last (hs_copy C pW censusTotal e (by decide)) ?_
  rintro f rfl n4 hn4
  have hfr : FrS a (e.set pW (e.env censusTotal)) parameterHeaderT :=
    FrS.trans (FrS.weaken hbfr (by decide))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (hefr.toS _ (by decide) (by decide))
          ((Fr.set _ _ (by decide)).toS)))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), hefr _ (by decide) (by decide) (by decide),
      hdfr _ (by decide) (by decide) (by decide), hbl]
  · rw [DS.set_env_ne _ _ (by decide), hefr _ (by decide) (by decide) (by decide), hdmu]
  · rw [DS.set_env_ne _ _ (by decide), hefr _ (by decide) (by decide) (by decide),
      hdfr _ (by decide) (by decide) (by decide), hbj]
    rfl
  · rw [DS.set_env_ne _ _ (by decide), hefr _ (by decide) (by decide) (by decide), hdm]
    rfl
  · rw [DS.set_env_ne _ _ (by decide), her]
    simp only [AE.eval, hdmu]
  · rw [DS.set_env_self, hefr _ (by decide) (by decide) (by decide),
      hdfr _ (by decide) (by decide) (by decide), hbfr _ (by decide) (by decide)]
  · exact hecp.trans (hdcp.trans hbcp)
  · exact hewq.trans (hdwq.trans hbwq)
  · exact heout.trans (hdout.trans hbout)
  · exact Cst.set hec pW _ (by decide)
  · simp only [AE.cost] at hn2 hn3
    omega

end NearQuarticWires.StagePrep
