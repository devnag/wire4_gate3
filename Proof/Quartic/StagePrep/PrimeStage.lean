import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The executed greatest-degree and prime-scale searches

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- Every changed register in the exact searches of
`sec:params`, paper/paper.tex. -/
def primeStageT : List (Fin VV) :=
  [pSI,pSF,pX5,pX6,pDM,vJ,t3,t5,t6,coefficientBitsReg,vADM] ++
    (pP :: pX7 :: pPF :: pX8 :: liftSavedKReg :: pK :: pEB :: liftVT)

/-- The exact degree and prime searches of `sec:params`,
paper/paper.tex, retain the selected degree,
coefficient exponent and greatest scale, with an exact public
acceptance flag even when no scale passes. -/
theorem preparationPrimeStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n m k ell N Q S J X BN : ℕ)
    (hnv : a.env vN=n) (hmv : a.env mReg=m) (hkv : a.env pK=k)
    (hellv : a.env degreeLogReg=ell) (hNv : a.env nSideReg=N)
    (hQv : a.env qReg=Q) (hSv : a.env seedLengthReg=S)
    (hJv : a.env pJM=J) (hXv : a.env xMaxReg=X)
    (ha : a.env vADM=1) (hQ : 0<Q)
    (hBN : BN=S+m*k+2*m*Nat.clog 2 (N^2*Q)+1)
    (hdeg : 100*(m*k+2+n*ell)+n+k+256 < 2^C.Wd)
    (hcoeff : 2*N*N*Q+S+m*k+2*m*Nat.clog 2 (N*N*Q)+2*m+32 < 2^C.Wd)
    (hlift : 3*(BN-1)+4 < C.Wd)
    (hpow : ∀ j≤2*BN, n^j < 2^C.Wd)
    (hprime : primeDegreeMaximum BN n J m X+2*(BN+1)+(2*J+2)+n+4*m+256 < 2^C.Wd) :
    let D := Nat.findGreatest (fun d => 100*(m*k+2+d*ell)≤n-k) n
    let P := Nat.findGreatest (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D) n
    Hs C preparationPrimeStage a
      (400*(n+2)+5*Nat.clog 2 (N*N*Q)+primeSearchCost BN n+140) (fun b =>
        b.env pDM=D ∧ b.env coefficientBitsReg=BN ∧ b.env pP=P ∧
        b.env pK=k ∧ b.env vADM=bnat (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D P) ∧
        b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ FrS a b primeStageT) := by
  dsimp only
  let D := Nat.findGreatest (fun d => 100*(m*k+2+d*ell)≤n-k) n
  let P := Nat.findGreatest (Cells.ParameterArithmetic.PrimeCandidate n BN J m X D) n
  have hBNpos : 1≤BN := by omega
  unfold preparationPrimeStage preparationSequence
  refine Hx.hs (Hs.then (degreeSearchProgram_spec C a hc n m k ell hnv hmv hkv hellv hdeg)
    (fun b ⟨hbD,hbcp,hbwq,hbout,hbc,hbfr⟩ n1 hn1 => ?_))
  have hbN : b.env nSideReg=N := (hbfr _ (by decide) (by decide)).trans hNv
  have hbQ : b.env qReg=Q := (hbfr _ (by decide) (by decide)).trans hQv
  have hbS : b.env seedLengthReg=S := (hbfr _ (by decide) (by decide)).trans hSv
  have hbm : b.env mReg=m := (hbfr _ (by decide) (by decide)).trans hmv
  have hbk : b.env pK=k := (hbfr _ (by decide) (by decide)).trans hkv
  refine Hs.then (coefficientBitsProgram_spec C b hbc N Q S m k hbN hbQ hbS hbm hbk hQ hcoeff)
    (fun d ⟨hdBN,hdcp,hdwq,hdout,hdc,hdfr⟩ n2 hn2 => ?_)
  have hdBN' : d.env coefficientBitsReg=BN := hdBN.trans hBN.symm
  have hdn : d.env vN=n := by simp (disch:=decide) only [hdfr.ev,hbfr.ev]; exact hnv
  have hdm : d.env mReg=m := (hdfr _ (by decide) (by decide)).trans hbm
  have hdk : d.env pK=k := (hdfr _ (by decide) (by decide)).trans hbk
  have hdJ : d.env pJM=J := by simp (disch:=decide) only [hdfr.ev,hbfr.ev]; exact hJv
  have hdX : d.env xMaxReg=X := by simp (disch:=decide) only [hdfr.ev,hbfr.ev]; exact hXv
  have hdD : d.env pDM=D := (hdfr _ (by decide) (by decide)).trans hbD
  refine Hs.then (primeSearchProgram_spec C d hdc BN n J m X D k hdBN' hdn hdJ hdm hdX hdD hdk
    hBNpos hlift hpow hprime)
    (fun e ⟨heP,hePF,heK,hecp,hewq,heout,hec,hefr⟩ n3 hn3 => ?_)
  have heA : e.env vADM=bnat True := by
    simp (disch:=decide) only [hefr.ev,hdfr.ev,hbfr.ev]
    rw [ha]
    decide
  refine Hs.then (needEq_spec pPF v1 (by decide) e True heA)
    (fun f ⟨hfA,hfcp,hfwq,hfout,hffr⟩ n4 hn4 => ?_)
  have hfc : Cst f := Cst.of_fr hec hffr (by decide)
    (by rw [hffr vPOS (by decide),hfcp]; exact hec.pos)
  refine Hs.last (skip_spec f) ?_
  rintro z rfl n5 hn5
  have F : FrS a f primeStageT :=
    FrS.trans (FrS.weaken hbfr (by decide))
      (FrS.trans (FrS.weaken hdfr (by decide))
        (FrS.trans (FrS.weaken hefr (by decide)) (FrS.weaken hffr.toS (by decide))))
  refine ⟨⟨?_,?_,?_,?_,?_,hfcp.trans (hecp.trans (hdcp.trans hbcp)),
    hfwq.trans (hewq.trans (hdwq.trans hbwq)),hfout.trans (heout.trans (hdout.trans hbout)),
    hfc.set _ _ (by decide),FrS.trans F (Fr.toS (Fr.set _ _ (by decide)))⟩,by omega⟩
  · simp (disch:=decide) only [DS.set_env_ne,hffr.ev,hefr.ev]
    exact hdD
  · simp (disch:=decide) only [DS.set_env_ne,hffr.ev,hefr.ev]
    exact hdBN'
  · simp (disch:=decide) only [DS.set_env_ne,hffr.ev]
    exact heP
  · simp (disch:=decide) only [DS.set_env_ne,hffr.ev]
    exact heK
  · rw [DS.set_env_ne _ _ (by decide),hfA,hePF,hec.one]
    apply bnat_congr
    simp only [true_and,bnat_eq_one]
    rfl

end NearQuarticWires.StagePrep
