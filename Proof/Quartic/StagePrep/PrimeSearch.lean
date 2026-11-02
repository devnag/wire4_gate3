import Proof.Quartic.StagePrep.PrimeCandidate

/-!
# The exact greatest prime-scale search

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The candidate scale search of `sec:params`, paper/paper.tex, scans down from the original arity and checks
the selected predicate once more for the public failure flag. -/
def primeSearchProgram : St VV :=
  .seq (.op (.copy pP vN))
    (.seq (fgScan pP pPF primeCandidateProgram) primeCandidateProgram)

/-- The finite search work of `sec:params`, paper/paper.tex, includes every lifted predicate evaluation. -/
def primeSearchCost (BN n : ℕ) : ℕ :=
  (n + 4) * (liftCost (BN - 1) + 520) + 100

/-- The program in `sec:params`, paper/paper.tex, computes the literal greatest scale and its exact
candidate flag, including a failed search returning zero. -/
theorem primeSearchProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (BN n J m X D k : ℕ)
    (hBNv : a.env coefficientBitsReg = BN) (hnv : a.env vN = n)
    (hJv : a.env pJM = J) (hmv : a.env mReg = m)
    (hXv : a.env xMaxReg = X) (hDv : a.env pDM = D) (hkv : a.env pK = k)
    (hBN : 1 ≤ BN) (hwidth : 3 * (BN - 1) + 4 < C.Wd)
    (hpow : ∀ j ≤ 2 * BN, n ^ j < 2 ^ C.Wd)
    (hW : primeDegreeMaximum BN n J m X + 2 * (BN + 1) +
      (2 * J + 2) + n + 4 * m + 256 < 2 ^ C.Wd) :
    Hs C primeSearchProgram a (primeSearchCost BN n) (fun b =>
      b.env pP = Nat.findGreatest (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D) n ∧
      b.env pPF = bnat (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D
        (Nat.findGreatest (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D) n)) ∧
      b.env pK = k ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b (pP :: pX7 :: pPF :: pX8 :: liftSavedKReg :: pK :: pEB :: liftVT)) := by
  let T := pP :: pX7 :: pPF :: pX8 :: liftSavedKReg :: pK :: pEB :: liftVT
  let PC := Cells.ParameterArithmetic.PrimeCandidate n BN J m X D
  let I : DS VV → Prop := fun b =>
    b.env vN = n ∧ b.env coefficientBitsReg = BN ∧ b.env pJM = J ∧
    b.env mReg = m ∧ b.env xMaxReg = X ∧ b.env pDM = D ∧ b.env pK = k ∧
    Cst b ∧ FrS a b T
  have hset : ∀ (x : Fin VV), x ∈ [pP, pPF] → ∀ b v, I b → I (b.set x v) := by
    rintro x hx b v ⟨hbn, hbBN, hbJ, hbm, hbX, hbD, hbK, hbc, hbfr⟩
    have hx' : x = pP ∨ x = pPF := by simpa using hx
    rcases hx' with rfl | rfl
    all_goals
      exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hbn,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbBN,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbJ,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbm,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbX,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbD,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbK,
        hbc.set _ _ (by decide), FrS.trans hbfr (Fr.toS (Fr.set _ _ (by decide)))⟩
  have htest : FlagTest C primeCandidateProgram pP pPF PC I (liftCost (BN - 1) + 500) n := by
    rintro b ⟨hbn, hbBN, hbJ, hbm, hbX, hbD, hbK, hbc, hbfr⟩ hv
    refine Hs.mono (primeCandidateProgram_spec C b hbc BN n J m X D (b.env pP) k
      hbBN hbn hbJ hbm hbX hbD rfl hbK hBN hv hwidth hpow hW) le_rfl ?_
    rintro d ⟨hdf, hdP, hdK, hdcp, hdwq, hdout, hdc, hdfr⟩
    refine ⟨hdf, hdP, ?_, hdcp, hdwq, hdout⟩
    exact ⟨(hdfr _ (by decide) (by decide)).trans hbn,
      (hdfr _ (by decide) (by decide)).trans hbBN,
      (hdfr _ (by decide) (by decide)).trans hbJ,
      (hdfr _ (by decide) (by decide)).trans hbm,
      (hdfr _ (by decide) (by decide)).trans hbX,
      (hdfr _ (by decide) (by decide)).trans hbD, hdK,
      hdc, FrS.trans hbfr (FrS.weaken hdfr (by decide))⟩
  unfold primeSearchProgram
  refine Hx.hs (Hs.then (hs_copy C pP vN a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hI : I (a.set pP (a.env vN)) :=
    ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hnv,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hBNv,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hJv,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hmv,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hXv,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hDv,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hkv,
      hc.set _ _ (by decide), Fr.toS (Fr.set _ _ (by decide))⟩
  refine Hs.then (fgScan_spec pP pPF (by decide) (by decide) (by decide) (by decide)
    primeCandidateProgram PC I (liftCost (BN - 1) + 500)
    (fun b hb => hb.2.2.2.2.2.2.2.1)
    (hset pPF (by simp)) (hset pP (by simp)) n htest _ hI
    (by rw [DS.set_env_self, hnv]))
    (fun b ⟨hbP, hbI, hbcp, hbwq, hbout⟩ n1 hn1 => ?_)
  obtain ⟨hbn, hbBN, hbJ, hbm, hbX, hbD, hbK, hbc, hbfr⟩ := hbI
  have hchosen : b.env pP ≤ n := by rw [hbP]; exact Nat.findGreatest_le _
  refine Hs.last (primeCandidateProgram_spec C b hbc BN n J m X D (b.env pP) k
    hbBN hbn hbJ hbm hbX hbD rfl hbK hBN hchosen hwidth hpow hW)
    (fun d ⟨hdf, hdP, hdK, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  refine ⟨⟨hdP.trans hbP, ?_, hdK, hdcp.trans hbcp, hdwq.trans hbwq,
    hdout.trans hbout, hdc, FrS.trans hbfr (FrS.weaken hdfr (by decide))⟩, ?_⟩
  · simpa only [hbP] using hdf
  · unfold primeSearchCost
    nlinarith only [hn0, hn1, hn2]

end NearQuarticWires.StagePrep
