import Proof.Quartic.StagePrep.LiftProgram
import Proof.Quartic.StagePrep.PrimeBudget
import Proof.Quartic.Cells.Parameters

/-!
# The finite prime-scale candidate predicate

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- One candidate evaluation in `sec:params`, paper/paper.tex, first checks the literal lower scale100. -/
def primeCandidateProgram : St VV :=
  .seq (assign pX7 (lit 100)) (.ite (.lt pP pX7) (.op (.zero pPF))
    (.seq liftExponentProgram primeBudgetProgram))

/-- The candidate evaluation of `sec:params`, paper/paper.tex, computes the actual canonical predicate while
preserving the star dimension and all public source fields. -/
theorem primeCandidateProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (BN n J m X D P k : ℕ)
    (hBNv : a.env coefficientBitsReg = BN) (hnv : a.env vN = n)
    (hJv : a.env pJM = J) (hmv : a.env mReg = m)
    (hXv : a.env xMaxReg = X) (hDv : a.env pDM = D)
    (hPv : a.env pP = P) (hkv : a.env pK = k)
    (hBN : 1 ≤ BN) (hPn : P ≤ n)
    (hwidth : 3 * (BN - 1) + 4 < C.Wd)
    (hpow : ∀ j ≤ 2 * BN, n ^ j < 2 ^ C.Wd)
    (hW : primeDegreeMaximum BN n J m X + 2 * (BN + 1) +
      (2 * J + 2) + n + 4 * m + 256 < 2 ^ C.Wd) :
    Hs C primeCandidateProgram a (liftCost (BN - 1) + 500) (fun b =>
      b.env pPF = bnat (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D P) ∧
      b.env pP = P ∧ b.env pK = k ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b (pX7 :: pPF :: pX8 :: liftSavedKReg :: pK :: pEB :: liftVT)) := by
  let T := pX7 :: pPF :: pX8 :: liftSavedKReg :: pK :: pEB :: liftVT
  unfold primeCandidateProgram
  refine Hx.hs (Hs.then (assign_spec pX7 (by decide) (by decide) (.lit 100) a
    (by aevar) (by aevar) hc (by aeok []))
    (fun b ⟨hb100, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hb100' : b.env pX7 = 100 := hb100
  have hbP : b.env pP = P := (hbfr _ (by decide) (by decide) (by decide)).trans hPv
  have hbK : b.env pK = k := (hbfr _ (by decide) (by decide) (by decide)).trans hkv
  let R : DS VV → Prop := fun d =>
    d.env pPF = bnat (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D P) ∧
    d.env pP = P ∧ d.env pK = k ∧
    d.cp = b.cp ∧ d.wq = b.wq ∧ d.out = b.out ∧ Cst d ∧ FrS b d T
  have hbranch : Hs C (.ite (.lt pP pX7) (.op (.zero pPF))
      (.seq liftExponentProgram primeBudgetProgram)) b (liftCost (BN - 1) + 242) R := by
    refine Hs.ite (c := .lt pP pX7) (show pP ≠ pX7 by decide) ?_ ?_
    · intro hlow
      have hP100 : P < 100 := by simpa only [Cnd.eval, hbP, hb100', decide_eq_true_eq] using hlow
      have hnot : ¬ Cells.ParameterArithmetic.PrimeCandidate n BN J m X D P := by
        intro hp
        have h := hp.1
        omega
      refine Hs.mono (hs_zero C pPF b) (by omega) ?_
      rintro d rfl
      exact ⟨by simp [bnat, hnot], by rw [DS.set_env_ne _ _ (by decide), hbP],
        by rw [DS.set_env_ne _ _ (by decide), hbK], rfl, rfl, rfl,
        hbc.set _ _ (by decide), Fr.toS (Fr.set _ _ (by decide))⟩
    · intro hhigh
      have hP100 : 100 ≤ P := by
        simp only [Cnd.eval, hbP, hb100', decide_eq_false_iff_not] at hhigh
        omega
      have hbBN : b.env coefficientBitsReg = BN := (hbfr _ (by decide) (by decide) (by decide)).trans hBNv
      refine Hs.seq (t1 := liftCost (BN - 1) + 40) (t2 := 200)
        (liftExponentProgram_spec C b hbc BN P k hbBN hbP hbK hBN (by omega)
        hwidth (fun j hj => (Nat.pow_le_pow_left hPn j).trans_lt (hpow j hj))) ?_
      rintro d ⟨_, hdSome, hdK, hdP, hdcp, hdwq, hdout, hdc, hdfr⟩
      have hdJ : d.env pJM = J := by
        rw [hdfr _ (by decide) (by decide), hbfr _ (by decide) (by decide) (by decide), hJv]
      have hdm : d.env mReg = m := by
        rw [hdfr _ (by decide) (by decide), hbfr _ (by decide) (by decide) (by decide), hmv]
      have hdX : d.env xMaxReg = X := by
        rw [hdfr _ (by decide) (by decide), hbfr _ (by decide) (by decide) (by decide), hXv]
      have hdD : d.env pDM = D := by
        rw [hdfr _ (by decide) (by decide), hbfr _ (by decide) (by decide) (by decide), hDv]
      have heSpec := Cells.ParameterArithmetic.liftExponent_spec BN P (d.env pE) hdSome
      refine Hs.mono (primeBudgetProgram_spec C d hdc BN n J m X D (d.env pE) P
        hdJ hdm hdX hdD rfl hdP heSpec.1.1 heSpec.2.1 (by omega) hPn hW) le_rfl ?_
      rintro e ⟨hef, hecp, hewq, heout, hec, hefr⟩
      have hiff : Cells.ParameterArithmetic.PrimeCandidate n BN J m X D P ↔
          (2 * d.env pE - 1) * (2 * J + 2) * (P - 1) + 4 * m * X ≤ D := by
        unfold Cells.ParameterArithmetic.PrimeCandidate
        rw [hdSome]
        simp only [hP100, hPn, true_and]
      refine ⟨?_, (hefr _ (by decide) (by decide)).trans hdP,
        (hefr _ (by decide) (by decide)).trans hdK,
        hecp.trans hdcp, hewq.trans hdwq, heout.trans hdout, hec,
        FrS.trans (FrS.weaken hdfr (by decide)) (FrS.weaken hefr (by decide))⟩
      rw [hef]
      exact bnat_congr hiff.symm
  refine Hs.last hbranch (fun d ⟨hdf, hdP, hdK, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  refine ⟨⟨hdf, hdP, hdK, hdcp.trans hbcp, hdwq.trans hbwq, hdout.trans hbout, hdc,
    FrS.trans (hbfr.toS _ (by decide) (by decide)) hdfr⟩, ?_⟩
  simp only [AE.cost] at hn1
  omega

end NearQuarticWires.StagePrep
