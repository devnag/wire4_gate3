import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.StagePrep.LiftRule
import Proof.Gates.Dispatch.ParamsC

/-!
# Physical computation of the lifted-prime exponent

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The preserved star dimension during the lift computation of
`sec:params`, paper/paper.tex. -/
def liftSavedKReg : Fin VV := ⟨96, by decide⟩

/-- The exact lifted-prime exponent computation of
`sec:params`, paper/paper.tex. -/
def liftExponentProgram : St VV :=
  .seq (.op (.copy liftSavedKReg pK))
    (.seq (assign pK (sub (var coefficientBitsReg) (lit 1)))
      (.seq (assign pEB (mul (lit 2) (var coefficientBitsReg)))
        (.seq liftV (.op (.copy pK liftSavedKReg)))))

/-- The lifted-prime exponent of `sec:params`,
paper/paper.tex, is computed by an actual finite
integer search; the star dimension is restored afterward. -/
theorem liftExponentProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (BN P k : ℕ) (hBNv : a.env coefficientBitsReg = BN)
    (hPv : a.env pP = P) (hkv : a.env pK = k)
    (hBN : 1 ≤ BN) (hP : 4 ≤ P)
    (hwidth : 3 * (BN - 1) + 4 < C.Wd)
    (hpow : ∀ j ≤ 2 * BN, P ^ j < 2 ^ C.Wd) :
    Hs C liftExponentProgram a (liftCost (BN - 1) + 40) (fun b =>
      b.env pEF = 1 ∧ Cells.ParameterArithmetic.liftExponent BN P = some (b.env pE) ∧
      b.env pK = k ∧ b.env pP = P ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b (liftSavedKReg :: pK :: pEB :: liftVT)) := by
  have hwidthPow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have h2BN : 2 * BN < 2 ^ C.Wd := by omega
  unfold liftExponentProgram
  refine Hx.hs (Hs.then (hs_copy C liftSavedKReg pK a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set liftSavedKReg (a.env pK)) := hc.set _ _ (by decide)
  have hcoef0 : (a.set liftSavedKReg (a.env pK)).env coefficientBitsReg = BN := by
    rw [DS.set_env_ne _ _ (by decide), hBNv]
  refine Hs.then (assign_spec pK (by decide) (by decide)
    (.sub (.var coefficientBitsReg) (.lit 1)) _ (by aevar) (by aevar) hc0 (by aeok []))
    (fun d ⟨hdk, hdfr, hdcp, hdwq, hdout, hdc⟩ n1 hn1 => ?_)
  have hdk' : d.env pK = BN - 1 := by simpa only [AE.eval, hcoef0] using hdk
  have hdBN : d.env coefficientBitsReg = BN :=
    (hdfr _ (by decide) (by decide) (by decide)).trans hcoef0
  have hdP : d.env pP = P := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_ne _ _ (by decide), hPv]
  have hdsaved : d.env liftSavedKReg = k := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_self, hkv]
  refine Hs.then (assign_spec pEB (by decide) (by decide)
    (.mul (.lit 2) (.var coefficientBitsReg)) d (by aevar) (by aevar) hdc (by aeok [hdBN]))
    (fun e ⟨heb, hefr, hecp, hewq, heout, hec⟩ n2 hn2 => ?_)
  have heb' : e.env pEB = 2 * BN := by simpa only [AE.eval, hdBN] using heb
  have heK : e.env pK = BN - 1 := (hefr _ (by decide) (by decide) (by decide)).trans hdk'
  have heP : e.env pP = P := (hefr _ (by decide) (by decide) (by decide)).trans hdP
  have hesaved : e.env liftSavedKReg = k := (hefr _ (by decide) (by decide) (by decide)).trans hdsaved
  refine Hs.then (liftV_spec e hec (BN - 1) P heP heK
    (by rw [heb', Nat.sub_add_cancel hBN]) hwidth
    (by simpa only [Nat.sub_add_cancel hBN] using hpow))
    (fun f ⟨hresult, hfP, _, _, hfcp, hfwq, hfout, hfc, hffr⟩ n3 hn3 => ?_)
  have hsuccess : f.env pEF = 1 ∧
      Cells.ParameterArithmetic.liftExponent BN P = some (f.env pE) := by
    rcases hresult with ⟨hflag, hsome⟩ | ⟨_, hnone⟩
    · exact ⟨hflag, by rwa [liftExp_eq_liftExponent BN P hBN hP] at hsome⟩
    · obtain ⟨j, hj⟩ := Cells.ParameterArithmetic.liftExponent_isSome BN P hP
      rw [liftExp_eq_liftExponent BN P hBN hP, hj] at hnone
      cases hnone
  have hfsaved : f.env liftSavedKReg = k := (hffr _ (by decide) (by decide)).trans hesaved
  refine Hs.last (hs_copy C pK liftSavedKReg f (by decide)) ?_
  rintro g rfl n4 hn4
  refine ⟨⟨?_, ?_, ?_, ?_, hfcp.trans (hecp.trans hdcp),
    hfwq.trans (hewq.trans hdwq), hfout.trans (heout.trans hdout),
    hfc.set _ _ (by decide), ?_⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide)]
    exact hsuccess.1
  · rw [DS.set_env_ne _ _ (by decide)]
    exact hsuccess.2
  · rw [DS.set_env_self, hfsaved]
  · rw [DS.set_env_ne _ _ (by decide), hfP]
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (hefr.toS _ (by decide) (by decide))
          (FrS.trans (FrS.weaken hffr (by decide)) (Fr.toS (Fr.set _ _ (by decide))))))
  · simp only [AE.cost] at hn1 hn2
    omega

end NearQuarticWires.StagePrep
