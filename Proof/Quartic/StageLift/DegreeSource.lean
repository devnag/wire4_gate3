import Proof.Quartic.StageLift.DegreeProgram
import Proof.Quartic.StageLift.IndexModulus

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:print` and `sec:params`, paper/paper.tex: the degree metadata is loaded from the three actual
retained parameter positions and the actual parsed index prime. -/
def readDegreeFields : St VV MM :=
  .seq (StageCertTests.selectParameter 12 degreeInput)
    (.seq (StageCertTests.selectParameter 26 degreeExponent)
      (.seq (StageCertTests.selectParameter 40 degreeChain)
        (.op (.copy degreePrime indexPrimeVar))))

/-- `lem:print` and `sec:params`, paper/paper.tex: each scalar is physically selected with its head
return and sequential read cost; no decoded degree field is supplied. -/
theorem readDegreeFields_spec (C : Ctx) (p : Cells.Parameters) (prime : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hparams : a.ram parameterStore = parameterScalars p)
    (hprime : a.env indexPrimeVar = prime) :
    Hs C readDegreeFields a (a.rc parameterStore + 300) (fun b =>
      b.env degreeInput = p.Xmax ∧ b.env degreeExponent = p.e ∧
      b.env degreeChain = p.J ∧ b.env degreePrime = prime ∧
      b.rc parameterStore = 41 ∧ b.ram = a.ram ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [degreeInput, degreeExponent, degreeChain, degreePrime, vJ]) := by
  unfold readDegreeFields
  have hx := StageCertTests.selectParameter_spec C a (parameterScalars p) 12
    (by rw [parameterScalars_length]; decide) degreeInput hparams
  refine (Hs.seq (t1 := a.rc parameterStore + 29) (t2 := 190) hx
    fun b ⟨hbX, hbcur, hbram, hbsh, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hb : b.env degreeInput = p.Xmax := by
    simpa [parameterScalars, parameterHeadScalars, parameterTailScalars,
      rationalFields, integerFields] using hbX
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have he := StageCertTests.selectParameter_spec C b (parameterScalars p) 26
    (by rw [parameterScalars_length]; decide) degreeExponent (by rw [hbram]; exact hparams)
  rw [hbcur] at he
  refine (Hs.seq (t1 := 70) (t2 := 117) he
    fun d ⟨hde, hdcur, hdram, hdsh, hdf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hd : d.env degreeExponent = p.e := by
    simpa [parameterScalars, parameterHeadScalars, parameterTailScalars,
      rationalFields, integerFields] using hde
  have hdc : Cst d := Cst.of_fr hbc hdf (by decide)
  have hj := StageCertTests.selectParameter_spec C d (parameterScalars p) 40
    (by rw [parameterScalars_length]; decide) degreeChain (by rw [hdram, hbram]; exact hparams)
  rw [hdcur] at hj
  refine (Hs.seq (t1 := 112) (t2 := 1) hj
    fun e ⟨heJ, hecur, heram, hesh, hef⟩ => ?_).mono (by omega) (fun _ h => h)
  have hec : Cst e := Cst.of_fr hdc hef (by decide)
  have heJ' : e.env degreeChain = p.J := by
    simpa [parameterScalars, parameterHeadScalars, parameterTailScalars,
      rationalFields, integerFields] using heJ
  refine (hs_copy C degreePrime indexPrimeVar e (by decide)).mono le_rfl ?_
  rintro f rfl
  have hff : Fr a (e.set degreePrime (e.env indexPrimeVar))
      [degreeInput, degreeExponent, degreeChain, degreePrime, vJ] :=
    (hbf.weaken (by simp)).trans ((hdf.weaken (by simp)).trans
      ((hef.weaken (by simp)).trans (Fr.set _ _ (by simp))))
  refine ⟨?_, ?_, ?_, ?_, hecur, heram.trans (hdram.trans hbram),
    hesh.trans (hdsh.trans hbsh), Cst.of_fr (T := [degreePrime]) hec
      (Fr.set _ _ (by simp)) (by decide), hff⟩
  · rw [DS.set_env_ne _ _ (by decide), hef _ (by decide), hdf _ (by decide)]
    exact hb
  · rw [DS.set_env_ne _ _ (by decide), hef _ (by decide)]
    exact hd
  · rw [DS.set_env_ne _ _ (by decide)]
    exact heJ'
  · change e.env indexPrimeVar = prime
    rw [hef _ (by decide), hdf _ (by decide), hbf _ (by decide)]
    exact hprime

/-- `lem:print`, paper/paper.tex: the actual
source fields supply the literal degree header by binary computation. -/
def computePrintDegree : St VV MM := .seq readDegreeFields computeResidueDegree

/-- `lem:print` and `sec:params`, paper/paper.tex: the executable source produces D itself, instead of
requiring the computed degree as an input word or runtime oracle. -/
theorem computePrintDegree_spec {x : Cells.ParameterInput} (C : Ctx)
    (p : Cells.Parameters) (hs : Cells.ParameterRules x p) (prime : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hparams : a.ram parameterStore = parameterScalars p)
    (hprime : a.env indexPrimeVar = prime) (hp : 2 ≤ prime)
    (hroom : 16 * p.Xmax + (2 * p.e - 1) * (2 * (p.J + 1)) * prime +
      2 * p.e + 2 * (p.J + 1) + prime + 17 < 2 ^ C.Wd) :
    Hs C computePrintDegree a (a.rc parameterStore + 401) (fun b =>
      b.env degreeVar = residueDegreeBound p prime ∧ b.ram = a.ram ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      b.rc parameterStore = 41 ∧ Cst b ∧
      Fr a b [degreeInput, degreeExponent, degreeChain, degreePrime, degreeVar,
        degreeFactor, degreeTerm, degreeProduct, vJ]) := by
  unfold computePrintDegree
  refine Hs.seq (t2 := 100) (readDegreeFields_spec C p prime a hc hparams hprime)
    fun b ⟨hbX, hbe, hbJ, hbp, hbcur, hbram, hbsh, hbc, hbf⟩ => ?_
  refine (computeResidueDegree_spec C b hbc p.Xmax p.e p.J prime hs.e_pos hs.J_pos hp
    hbX hbe hbJ hbp hroom).mono le_rfl ?_
  rintro d ⟨hdd, hdsh, hdc, hdf⟩
  have hsame := Same.of_sh hdsh
  refine ⟨hdd, hsame.ram.trans hbram, ?_, by rw [hsame.rc, hbcur], hdc, ?_⟩
  · rw [hsame.ip, hsame.out, hsame.kin, hsame.kout, hsame.kc]
    exact hbsh
  · exact (hbf.weaken (by simp)).trans (hdf.weaken (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto))

end NearQuarticWires.StageLift
