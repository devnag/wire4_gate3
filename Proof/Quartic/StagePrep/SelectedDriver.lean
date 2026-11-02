import Proof.Quartic.StagePrep.ExecutionWidths
import Proof.Quartic.StagePrep.HeaderStage
import Proof.Quartic.StagePrep.PrintingGuard
import Proof.Quartic.StagePrep.PrimeStage
import Proof.Quartic.StagePrep.LiftGuard
import Proof.Quartic.StagePrep.WindowGuard
import Proof.Quartic.StagePrep.HeightGuard
import Proof.Quartic.StagePrep.ChainGuard
import Proof.Quartic.StagePrep.FinishGuard
import Proof.Quartic.StagePrep.ActiveGuard
import Proof.Quartic.StagePrep.ParameterMemory

/-!
# Execution of the complete selected parameter computation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- The register sets changed by the guarded computation in
`sec:params`, paper/paper.tex. -/
def selectedFrameBlocks : List (List (Fin VV)) :=
  [parameterHeaderT++[pX1,vADM,vJ], publicScalesT,
    [t3,t5,t6,atomsReg,childCapReg,occurrenceCapReg,vJ,degreeLogReg,pSI,pSF,pX5,pX6,vADM],
    primeStageT, pX1::vADM::liftSavedKReg::pK::pEB::liftVT,
    prT++pairT++[pLW,vJ,vADM], [pHE,pH,ellZeroReg,pX1,vADM,vJ],
    vADM::pX1::pX2::barT++chT, [pJ,pLB,vADM,vJ]]

/-- The full changed-register set of `sec:params`,
paper/paper.tex. -/
def selectedPreparationT : List (Fin VV) := selectedFrameBlocks.flatten

/-- The literal parsed call fields in `sec:params`,
paper/paper.tex, are outside the complete
parameter-computation register set. -/
theorem selectedPreparationT_preserves_call :
    ∀ r : Fin VV, 17≤r.val → r.val<56 → r∉selectedPreparationT := by
  decide

/-- The sum of every actual guarded stage in `sec:params`,
paper/paper.tex, including the repeated lift,
prime census, stopping search and all guard comparisons. -/
def selectedPreparationCost (x : Cells.ParameterInput) (p : Cells.Parameters)
    (num den : ℕ) : ℕ :=
  (20*x.n+250)+publicScalesCost x p num den+
    (5*Nat.clog 2 p.Uocc+480)+
    (400*(x.n+2)+5*Nat.clog 2 (p.N*p.N*p.Q)+primeSearchCost p.BN x.n+140)+
    (liftCost (p.BN-1)+200)+(primesCost p.P+pairCost p.Dprime+13)+400+
    (3024+chainCost (Jmax x.n) p.h)+63+28

/-- The exact memory of the whole canonical computation of
`sec:params`, paper/paper.tex, is obtained by
executing all nine actual guarded stages. No running-time or
program realization is assumed by the operand-capacity record. -/
theorem canonicalPreparation_selected_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (x : Cells.ParameterInput) (p : Cells.Parameters) (hs : Cells.ParameterRules x p)
    (num den w1 w2 S : ℕ) (hbn : x.beta.num=num) (hbd : x.beta.den=den)
    (hnv : a.env vN=x.n) (hw1 : a.env vTW1=w1) (hw2 : a.env vTW2=w2)
    (hcount : a.env censusTotal=x.W) (hnumv : a.env vNUM=num) (hdenv : a.env vDEN=den)
    (hG1v : a.env vG1=x.G1) (hG2v : a.env vG2=x.G2)
    (hBv : a.env vB0=NearCubicGates.Close.Counter.B0 x.n)
    (hTag : a.env vTAG=1 ↔ x.pair=true) (ha : a.env vADM=1)
    (hw : SelectedWidths C x p num den w1 w2 S) :
    Hs C canonicalPreparation a (selectedPreparationCost x p num den) (fun b =>
      RegisterValues b (parameterMemoryValues p) ∧ b.env vADM=1 ∧
      firstRatio p.ell0 p.h p.T=(b.env pXN:ℚ)/b.env pXD ∧
      0<b.env pXN ∧ b.env pXN≤b.env pXD ∧ b.env pXD≤(p.h+32)*b.env pXN ∧
      b.env pXD<2^(5*S+22) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ FrS a b selectedPreparationT) := by
  have hs0 : Cells.CoreRules x p := hs
  have hdenpos : 0<den := by rw [←hbd]; exact x.beta.den_pos
  have hnumpos : 0<num := by
    have hpos := Rat.num_pos.mpr hs0.beta_pos
    rw [hbn] at hpos
    exact_mod_cast hpos
  have hrpos : 0<p.r := by have := hs0.r_even_large.2; omega
  have hkpos : 0<p.k := by
    rw [hs.k_eq]
    exact Nat.mul_pos hrpos (by rw [←hs0.star_s]; exact hs0.starParams.one_le_s)
  have htau : 0<p.tau := by rw [hs.tau_eq]; omega
  have hU : 0<p.U := by rw [hs.U_eq]; exact htau.trans_le (le_max_left ..)
  have hmpos : 0<p.m := by rw [hs.m_eq]; norm_num
  have hXpos : 0<p.Xmax := by
    have hsq := Cells.ParameterArithmetic.le_ceilSqrt_sq (9*p.tau^2*x.n*p.r)
    rw [←hs.Xmax_eq] at hsq
    have hnpos := hs0.n_pos
    have hrad : 0<9*p.tau^2*x.n*p.r := by positivity
    nlinarith
  have hQpos : 0<p.Q := by rw [hs.Q_eq]; positivity
  have hBNpos : 1≤p.BN := by rw [hs.BN_eq]; omega
  have hp100 : 100≤p.P := hs.prime_candidate.1
  have hpn : p.P≤x.n := hs.prime_candidate.2.1
  have hpowP : ∀ j≤2*p.BN,p.P^j<2^C.Wd := fun j hj =>
    (Nat.pow_le_pow_left hpn j).trans_lt (hw.powers j hj)
  have hJmax : p.Jmax=Jmax x.n := by rw [hs.Jmax_eq,hs.mu_eq]; rfl
  have hpa : printingAtomCount x.n p.m=p.NatAtoms := hs.NatAtoms_eq.symm
  have hpc : printingChildCount x.n (NearCubicGates.Close.Counter.B0 x.n) p.lambda=p.childCap := by
    rw [hs.childCap_eq]
    unfold printingChildCount Cells.childCap
    rw [hs.lambda_eq]
    rfl
  have hpo : printingOccurrenceCount x.n p.m (NearCubicGates.Close.Counter.B0 x.n) p.lambda=p.Uocc := by
    unfold printingOccurrenceCount
    rw [hpa,hpc,hs.Uocc_eq]
  have hpD : p.Dmax=Nat.findGreatest (fun d =>
      100*(p.m*p.k+2+d*Nat.clog 2 p.Uocc)≤x.n-p.k) x.n := hs.Dmax_eq
  have hpflen : p.factors.length=p.J-1 := by rw [hs.factors_eq]; simp [chainFactors]
  have hell : p.ell0=(32*p.m*p.U:ℕ) := hs.ell0_eq
  have hellpos : 0<32*p.m*p.U := by positivity
  have hhpos : 0<p.h := by have := hs.height; have := hs0.T_pos; omega
  unfold canonicalPreparation guardedPreparationStages
  have in1_n : a.env vN=x.n := by
    exact hnv
  have in1_w1 : a.env vTW1=w1 := by
    exact hw1
  have in1_w2 : a.env vTW2=w2 := by
    exact hw2
  refine Hx.hs (Hs.then (activeGuard_spec C a hc preparationHeaderStage _ _ ha
    (preparationHeaderStage_spec C a hc x.n w1 w2 in1_n in1_w1 in1_w2 ha hw.header))
    (fun s1 ⟨raw_lam,raw_mu,raw_Jmax,raw_m,raw_r,raw_W,raw_flag,cp1,wq1,out1,c1,f1⟩ n1 hn1 => ?_))
  have v1_lambda : s1.env pLAM=p.lambda := by simpa only [hs.lambda_eq] using raw_lam
  have v1_mu : s1.env pMU=p.mu := by simpa only [hs.mu_eq] using raw_mu
  have v1_Jmax : s1.env pJM=p.Jmax := by simpa only [hs.Jmax_eq,hs.mu_eq] using raw_Jmax
  have v1_m : s1.env mReg=p.m := by simpa only [hs.m_eq] using raw_m
  have v1_r : s1.env rReg=p.r := by simpa only [hs.r_eq,hs.mu_eq] using raw_r
  have v1_W : s1.env pW=x.W := raw_W.trans hcount
  have flag1 : s1.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 (by simpa only [←hs.mu_eq,←hs.r_eq] using hs.r_bound)
  have in2_n : s1.env vN=x.n := by
    simp (disch:=decide) only [f1.ev]
    exact hnv
  have in2_r : s1.env rReg=p.r := by
    exact v1_r
  have in2_m : s1.env mReg=p.m := by
    exact v1_m
  have in2_Jmax : s1.env pJM=p.Jmax := by
    exact v1_Jmax
  have in2_W : s1.env pW=x.W := by
    exact v1_W
  have in2_num : s1.env vNUM=num := by
    simp (disch:=decide) only [f1.ev]
    exact hnumv
  have in2_den : s1.env vDEN=den := by
    simp (disch:=decide) only [f1.ev]
    exact hdenv
  have in2_G1 : s1.env vG1=x.G1 := by
    simp (disch:=decide) only [f1.ev]
    exact hG1v
  have in2_G2 : s1.env vG2=x.G2 := by
    simp (disch:=decide) only [f1.ev]
    exact hG2v
  refine Hs.then (activeGuard_spec C s1 c1 preparationScalesStage _ _ flag1
    (publicScalesProgram_spec C s1 c1 x p hs0 num den hbn hbd in2_n in2_r in2_m in2_Jmax in2_W in2_num in2_den in2_G1 in2_G2 hrpos htau hU hnumpos hw.early.dims hw.early.cwidth hw.early.cleft hw.early.cbound hw.early.cbits hw.early.tauW hw.early.uratio hw.early.uroot hw.early.piW hw.early.xroot hw.early.xcut hw.early.fourier hw.early.etaW hw.early.sample hw.early.Qexp hw.early.seed))
    (fun s2 ⟨raw_values,cp2,wq2,out2,c2,f2⟩ n2 hn2 => ?_)
  have v2_s : s2.env sReg=p.s := raw_values (sReg,p.s) (by simp [publicScaleValues])
  have v2_b : s2.env bReg=p.b := raw_values (bReg,p.b) (by simp [publicScaleValues])
  have v2_k : s2.env pK=p.k := raw_values (pK,p.k) (by simp [publicScaleValues])
  have v2_N : s2.env nSideReg=p.N := raw_values (nSideReg,p.N) (by simp [publicScaleValues])
  have v2_T : s2.env pT=p.T := raw_values (pT,p.T) (by simp [publicScaleValues])
  have v2_tau : s2.env tauReg=p.tau := raw_values (tauReg,p.tau) (by simp [publicScaleValues])
  have v2_U : s2.env pU=p.U := raw_values (pU,p.U) (by simp [publicScaleValues])
  have v2_piN : s2.env piNumReg=p.pi0.num.natAbs := raw_values (piNumReg,p.pi0.num.natAbs) (by simp [publicScaleValues])
  have v2_piD : s2.env piDenReg=p.pi0.den := raw_values (piDenReg,p.pi0.den) (by simp [publicScaleValues])
  have v2_X : s2.env xMaxReg=p.Xmax := raw_values (xMaxReg,p.Xmax) (by simp [publicScaleValues])
  have v2_d : s2.env dStarReg=p.dstar := raw_values (dStarReg,p.dstar) (by simp [publicScaleValues])
  have v2_o1 : s2.env omegaOneReg=p.omega1 := raw_values (omegaOneReg,p.omega1) (by simp [publicScaleValues])
  have v2_o2 : s2.env omegaTwoReg=p.omega2 := raw_values (omegaTwoReg,p.omega2) (by simp [publicScaleValues])
  have v2_MF : s2.env mFourierReg=p.MF := raw_values (mFourierReg,p.MF) (by simp [publicScaleValues])
  have v2_etaN : s2.env etaNumReg=p.eta.num.natAbs := raw_values (etaNumReg,p.eta.num.natAbs) (by simp [publicScaleValues])
  have v2_etaD : s2.env etaDenReg=p.eta.den := raw_values (etaDenReg,p.eta.den) (by simp [publicScaleValues])
  have v2_Qexp : s2.env qExponentReg=p.Qexp := raw_values (qExponentReg,p.Qexp) (by simp [publicScaleValues])
  have v2_Q : s2.env qReg=p.Q := raw_values (qReg,p.Q) (by simp [publicScaleValues])
  have v2_ellf : s2.env ellFieldReg=p.ellf := raw_values (ellFieldReg,p.ellf) (by simp [publicScaleValues])
  have v2_S : s2.env seedLengthReg=p.S := raw_values (seedLengthReg,p.S) (by simp [publicScaleValues])
  have flag2 : s2.env vADM=1 := by rw [f2 _ (by decide) (by decide)]; exact flag1
  have in3_n : s2.env vN=x.n := by
    simp (disch:=decide) only [f2.ev, f1.ev]
    exact hnv
  have in3_m : s2.env mReg=p.m := by
    simp (disch:=decide) only [f2.ev]
    exact v1_m
  have in3_B : s2.env vB0=NearCubicGates.Close.Counter.B0 x.n := by
    simp (disch:=decide) only [f2.ev, f1.ev]
    exact hBv
  have in3_lambda : s2.env pLAM=p.lambda := by
    simp (disch:=decide) only [f2.ev]
    exact v1_lambda
  have in3_k : s2.env pK=p.k := by
    exact v2_k
  refine Hs.then (activeGuard_spec C s2 c2 preparationDegreeStage _ _ flag2
    (preparationDegreeStage_spec C s2 c2 x.n p.m (NearCubicGates.Close.Counter.B0 x.n) p.lambda p.k in3_n in3_m in3_B in3_lambda in3_k flag2 hs0.n_pos (by simpa only [hpa,hpc] using hw.print) (by simpa only [hpo] using hw.log) (by simpa only [hpo] using hw.degree)))
    (fun s3 ⟨raw_atoms,raw_child,raw_occ,raw_log,raw_flag,cp3,wq3,out3,c3,f3⟩ n3 hn3 => ?_)
  have v3_atoms : s3.env atomsReg=p.NatAtoms := raw_atoms.trans hpa
  have v3_child : s3.env childCapReg=p.childCap := raw_child.trans hpc
  have v3_occ : s3.env occurrenceCapReg=p.Uocc := raw_occ.trans hpo
  have v3_log : s3.env degreeLogReg=Nat.clog 2 p.Uocc := by simpa only [hpo] using raw_log
  have flag3 : s3.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 (by simpa only [hpo] using hs.initial_degree)
  have in4_n : s3.env vN=x.n := by
    simp (disch:=decide) only [f3.ev, f2.ev, f1.ev]
    exact hnv
  have in4_m : s3.env mReg=p.m := by
    simp (disch:=decide) only [f3.ev, f2.ev]
    exact v1_m
  have in4_k : s3.env pK=p.k := by
    simp (disch:=decide) only [f3.ev]
    exact v2_k
  have in4_log : s3.env degreeLogReg=Nat.clog 2 p.Uocc := by
    exact v3_log
  have in4_N : s3.env nSideReg=p.N := by
    simp (disch:=decide) only [f3.ev]
    exact v2_N
  have in4_Q : s3.env qReg=p.Q := by
    simp (disch:=decide) only [f3.ev]
    exact v2_Q
  have in4_S : s3.env seedLengthReg=p.S := by
    simp (disch:=decide) only [f3.ev]
    exact v2_S
  have in4_Jmax : s3.env pJM=p.Jmax := by
    simp (disch:=decide) only [f3.ev, f2.ev]
    exact v1_Jmax
  have in4_X : s3.env xMaxReg=p.Xmax := by
    simp (disch:=decide) only [f3.ev]
    exact v2_X
  refine Hs.then (activeGuard_spec C s3 c3 preparationPrimeStage _ _ flag3
    (preparationPrimeStage_spec C s3 c3 x.n p.m p.k (Nat.clog 2 p.Uocc) p.N p.Q p.S p.Jmax p.Xmax p.BN in4_n in4_m in4_k in4_log in4_N in4_Q in4_S in4_Jmax in4_X flag3 hQpos hs.BN_eq hw.degree hw.coefficient hw.lift hw.powers hw.prime))
    (fun s4 ⟨raw_D,raw_BN,raw_P,raw_k,raw_flag,cp4,wq4,out4,c4,f4⟩ n4 hn4 => ?_)
  have v4_D : s4.env pDM=p.Dmax := by simpa only [←hpD] using raw_D
  have v4_BN : s4.env coefficientBitsReg=p.BN := raw_BN
  have v4_P : s4.env pP=p.P := by simpa only [←hpD,←hs.P_eq] using raw_P
  have v4_k : s4.env pK=p.k := raw_k
  have flag4 : s4.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 (by simpa only [←hpD,←hs.P_eq] using hs.prime_candidate)
  have in5_BN : s4.env coefficientBitsReg=p.BN := by
    exact v4_BN
  have in5_P : s4.env pP=p.P := by
    exact v4_P
  have in5_k : s4.env pK=p.k := by
    exact v4_k
  have in5_m : s4.env mReg=p.m := by
    simp (disch:=decide) only [f4.ev, f3.ev, f2.ev]
    exact v1_m
  have in5_X : s4.env xMaxReg=p.Xmax := by
    simp (disch:=decide) only [f4.ev, f3.ev]
    exact v2_X
  have in5_D : s4.env pDM=p.Dmax := by
    exact v4_D
  refine Hs.then (activeGuard_spec C s4 c4 preparationLiftStage _ _ flag4
    (preparationLiftStage_spec C s4 c4 p.BN p.P p.k p.m p.Xmax p.Dmax in5_BN in5_P in5_k in5_m in5_X in5_D flag4 hBNpos (by omega) hw.lift hpowP hmpos hXpos hw.moment))
    (fun s5 ⟨raw_e,raw_k,raw_P,raw_flag,cp5,wq5,out5,c5,f5⟩ n5 hn5 => ?_)
  have v5_eLift : s5.env pE=p.e := by rw [hs.e_eq] at raw_e; exact (Option.some.inj raw_e).symm
  have v5_k : s5.env pK=p.k := raw_k
  have v5_P : s5.env pP=p.P := raw_P
  have flag5 : s5.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 hs.moment_degree
  have in6_P : s5.env pP=p.P := by
    exact v5_P
  have tag6 : s5.env vTAG=1 ↔ x.pair=true := by
    simp (disch:=decide) only [f5.ev,f4.ev,f3.ev,f2.ev,f1.ev]
    exact hTag
  refine Hs.then (activeGuard_spec C s5 c5 preparationWindowsStage _ _ flag5
    (preparationWindowsStage_spec C s5 c5 p.P x.pair in6_P tag6 flag5 hw.primeCensus (by simpa only [←hs.primes_eq,←hs.Dprime_eq] using hw.pairWindow)))
    (fun s6 ⟨raw_card,raw_Dprime,raw_L2,raw_Lw,raw_P,raw_flag,cp6,wq6,out6,c6,f6⟩ n6 hn6 => ?_)
  have v6_card : s6.env pNP=p.primes.card := by simpa only [←hs.primes_eq] using raw_card
  have v6_Dprime : s6.env pWIN=p.Dprime := by simpa only [←hs.primes_eq,←hs.Dprime_eq] using raw_Dprime
  have v6_L2 : s6.env pL2=p.L2 := by simpa only [←hs.primes_eq,←hs.Dprime_eq,←hs.L2_eq] using raw_L2
  have v6_Lw : s6.env pLW=p.Lw := by simpa only [←hs.primes_eq,←hs.Dprime_eq,←hs.L2_eq,←hs.Lw_eq] using raw_Lw
  have v6_P : s6.env pP=p.P := raw_P
  have flag6 : s6.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 (by simpa only [←hs.primes_eq] using hs.primes_nonempty)
  have in7_P : s6.env pP=p.P := by
    exact v6_P
  have in7_m : s6.env mReg=p.m := by
    simp (disch:=decide) only [f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
    exact v1_m
  have in7_U : s6.env pU=p.U := by
    simp (disch:=decide) only [f6.ev, f5.ev, f4.ev, f3.ev]
    exact v2_U
  have in7_T : s6.env pT=p.T := by
    simp (disch:=decide) only [f6.ev, f5.ev, f4.ev, f3.ev]
    exact v2_T
  refine Hs.then (activeGuard_spec C s6 c6 preparationHeightStage _ _ flag6
    (preparationHeightStage_spec C s6 c6 p.P p.m p.U p.T in7_P in7_m in7_U in7_T flag6 hmpos hU hw.height hw.heightGuard))
    (fun s7 ⟨raw_hE,raw_h,raw_ell,raw_flag,cp7,wq7,out7,c7,f7⟩ n7 hn7 => ?_)
  have v7_hE : s7.env pHE=p.hE := by simpa only [←hs.hE_eq] using raw_hE
  have v7_h : s7.env pH=p.h := by simpa only [←hs.hE_eq,←hs.h_eq] using raw_h
  have v7_ellRaw : s7.env ellZeroReg=32*p.m*p.U := raw_ell
  have flag7 : s7.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 (by simpa only [←hs.hE_eq,←hs.h_eq] using hs.height)
  have in8_ellRaw : s7.env ellZeroReg=32*p.m*p.U := by
    exact v7_ellRaw
  have in8_h : s7.env pH=p.h := by
    exact v7_h
  have in8_T : s7.env pT=p.T := by
    simp (disch:=decide) only [f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
    exact v2_T
  have in8_Jmax : s7.env pJM=p.Jmax := by
    simp (disch:=decide) only [f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
    exact v1_Jmax
  refine Hs.then (activeGuard_spec C s7 c7 preparationChainStage _ _ flag7
    (preparationChainStage_spec C s7 c7 (32*p.m*p.U) p.h p.T S x.n in8_ellRaw in8_h in8_T (by simpa only [hJmax] using in8_Jmax) flag7 hellpos hhpos hs0.T_pos hs.height hw.ell hw.h hw.T (by simpa only [←hJmax] using hw.J) hw.chain))
    (fun s8 ⟨raw_M1,raw_flag,raw_stop,raw_A,raw_Acap,raw_CIcap,raw_ratio,raw_N0,raw_ND,raw_Dle,raw_Dcap,cp8,wq8,out8,c8,f8⟩ n8 hn8 => ?_)
  have hstop8 : stopIndex (firstRatio ((32*p.m*p.U:ℕ):ℚ) p.h p.T) x.n=some (p.J-1) := by
    simpa only [hell] using hs.chain_eq
  have ci8 : s8.env pCI=p.J-1 := by
    have hz := raw_stop (by rw [hstop8]; rfl)
    rw [hstop8] at hz
    exact (Option.some.inj hz).symm
  have v8_CI : s8.env pCI=p.factors.length := ci8.trans hpflen.symm
  have v8_A : s8.env pA=p.A := by
    rw [raw_A,ci8,←hell,←hs.factors_eq,←hs.A_eq]
  have v8_M1 : s8.env pM1=p.M1 := by simpa only [←hell,←hs.M1_eq] using raw_M1
  have flag8 : s8.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 (by rw [←hell,hs.chain_eq]; rfl)
  have in9_CI : s8.env pCI=p.factors.length := by
    exact v8_CI
  have in9_A : s8.env pA=p.A := by
    exact v8_A
  have in9_Lw : s8.env pLW=p.Lw := by
    simp (disch:=decide) only [f8.ev, f7.ev]
    exact v6_Lw
  have in9_Jmax : s8.env pJM=p.Jmax := by
    simp (disch:=decide) only [f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
    exact v1_Jmax
  refine Hs.then (activeGuard_spec C s8 c8 preparationFinishStage _ _ flag8
    (preparationFinishStage_spec C s8 c8 (p.J-1) p.A p.Lw p.Jmax (by simpa only [hpflen] using in9_CI) in9_A in9_Lw in9_Jmax flag8 hw.finish))
    (fun s9 ⟨raw_J,raw_Lambda,raw_A,raw_flag,cp9,wq9,out9,c9,f9⟩ n9 hn9 => ?_)
  have v9_Jfinal : s9.env pJ=p.J := by have := hs.J_pos; omega
  have v9_Lambda : s9.env pLB=p.Lambda := by simpa only [←hs.Lambda_eq] using raw_Lambda
  have v9_A : s9.env pA=p.A := raw_A
  have flag9 : s9.env vADM=1 := by rw [raw_flag]; exact (bnat_eq_one _).2 (by have := hs.J_pos; have := hs.J_bound; omega)
  refine Hs.last (skip_spec s9) ?_
  rintro z rfl n10 hn10
  have v7_ell : s7.env ellZeroReg=p.ell0.num.natAbs := by
    simpa only [hs.ell0_eq,Rat.num_natCast,Int.natAbs_natCast] using v7_ellRaw
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,c9.set _ _ (by decide),?_⟩,?_⟩
  · simp only [RegisterValues,parameterMemoryValues,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_lambda
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_mu
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_m
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_r
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_s
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_b
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev]
      exact v5_k
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_N
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_Jmax
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_T
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_tau
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_U
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_X
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_d
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_o1
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_o2
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_MF
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_Q
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_ellf
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_S
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev]
      exact v3_atoms
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev]
      exact v3_child
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev]
      exact v3_occ
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev]
      exact v4_D
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev]
      exact v4_BN
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev]
      exact v6_P
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev]
      exact v5_eLift
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev]
      exact v7_hE
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev]
      exact v7_h
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev]
      exact v6_Lw
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_piN
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_piD
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_etaN
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_etaD
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_Qexp
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev]
      exact v6_card
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev]
      exact v6_Dprime
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev, f7.ev]
      exact v6_L2
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev]
      exact v8_M1
    · rw [DS.set_env_ne _ _ (by decide)]
      exact v9_Jfinal
    · rw [DS.set_env_ne _ _ (by decide)]
      exact v9_A
    · rw [DS.set_env_ne _ _ (by decide)]
      exact v9_Lambda
    · rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev, f8.ev]
      exact v7_ell
    · rintro y rfl
      change (s9.set vJ 0).env pCI=p.factors.length
      rw [DS.set_env_ne _ _ (by decide)]
      simp (disch:=decide) only [f9.ev]
      exact v8_CI
  · rw [DS.set_env_ne _ _ (by decide),flag9]
  · simp (disch:=decide) only [DS.set_env_ne,f9.ev]
    simpa only [←hell] using raw_ratio
  · simp (disch:=decide) only [DS.set_env_ne,f9.ev]
    exact raw_N0
  · simp (disch:=decide) only [DS.set_env_ne,f9.ev]
    exact raw_ND
  · simp (disch:=decide) only [DS.set_env_ne,f9.ev]
    exact raw_Dle
  · simp (disch:=decide) only [DS.set_env_ne,f9.ev]
    exact raw_Dcap
  · change s9.cp=a.cp
    rw [cp9, cp8, cp7, cp6, cp5, cp4, cp3, cp2, cp1]
  · change s9.wq=a.wq
    rw [wq9, wq8, wq7, wq6, wq5, wq4, wq3, wq2, wq1]
  · change s9.out=a.out
    rw [out9, out8, out7, out6, out5, out4, out3, out2, out1]
  ·
    have F1 : FrS a s1 selectedPreparationT :=
      FrS.weaken f1 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F2 : FrS s1 s2 selectedPreparationT :=
      FrS.weaken f2 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F3 : FrS s2 s3 selectedPreparationT :=
      FrS.weaken f3 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F4 : FrS s3 s4 selectedPreparationT :=
      FrS.weaken f4 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F5 : FrS s4 s5 selectedPreparationT :=
      FrS.weaken f5 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F6 : FrS s5 s6 selectedPreparationT :=
      FrS.weaken f6 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F7 : FrS s6 s7 selectedPreparationT :=
      FrS.weaken f7 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F8 : FrS s7 s8 selectedPreparationT :=
      FrS.weaken f8 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F9 : FrS s8 s9 selectedPreparationT :=
      FrS.weaken f9 (by
        intro y hy
        exact List.mem_flatten.mpr ⟨_,by simp [selectedFrameBlocks],hy⟩)
    have F : FrS a s9 selectedPreparationT := FrS.trans (FrS.trans (FrS.trans (FrS.trans (FrS.trans (FrS.trans (FrS.trans (FrS.trans (F1) F2) F3) F4) F5) F6) F7) F8) F9
    exact FrS.trans F (Fr.toS (Fr.set _ _ (by decide)))
  · unfold selectedPreparationCost
    rw [hpo] at hn3
    have hwin : NearCubicGates.ScalarWindow.window (dyadicPrimes p.P)=p.Dprime := by rw [←hs.primes_eq,←hs.Dprime_eq]
    rw [hwin] at hn6
    omega

end NearQuarticWires.StagePrep
