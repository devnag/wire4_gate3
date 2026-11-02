import Proof.Quartic.StagePrep.DimensionsStage
import Proof.Quartic.StagePrep.ConcentrationProgram
import Proof.Quartic.StagePrep.TauProgram
import Proof.Quartic.StagePrep.UProgram
import Proof.Quartic.StagePrep.PiProgram
import Proof.Quartic.StagePrep.PopulationStage
import Proof.Quartic.StagePrep.FourierSizes
import Proof.Quartic.StagePrep.EtaProgram
import Proof.Quartic.StagePrep.SamplingStage
import Proof.Quartic.StagePrep.RegisterValues
import Proof.Quartic.Cells.ParametersPublic

/-!
# Execution of all early public parameter rules

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- The complete early scalar computation of `sec:params`,
paper/paper.tex, before the printing guard. -/
def publicScalesProgram : St VV :=
  .seq dimensionsStage (.seq concentrationProgram (.seq tauProgram (.seq uProgram
    (.seq piProgram (.seq populationStage (.seq fourierSizesProgram
      (.seq etaProgram samplingStage)))))))

/-- Registers containing the exact early fields of
`sec:params`, paper/paper.tex. -/
def publicScaleValues (p : Cells.Parameters) : List (Fin VV × ℕ) :=
  [(sReg,p.s),(bReg,p.b),(pK,p.k),(nSideReg,p.N),(pT,p.T),(tauReg,p.tau),(pU,p.U),
    (piNumReg,p.pi0.num.natAbs),(piDenReg,p.pi0.den),(xMaxReg,p.Xmax),(dStarReg,p.dstar),
    (omegaOneReg,p.omega1),(omegaTwoReg,p.omega2),(mFourierReg,p.MF),
    (etaNumReg,p.eta.num.natAbs),(etaDenReg,p.eta.den),(qExponentReg,p.Qexp),
    (qReg,p.Q),(ellFieldReg,p.ellf),(seedLengthReg,p.S)]

/-- Every changed register in the early computation of
`sec:params`, paper/paper.tex. -/
def publicScalesT : List (Fin VV) :=
  [LGX,LGR,LGT,sReg,vJ] ++ starDimensionsT ++
  (savedDimensionReg :: pK :: pT :: teeT) ++
  [rationalNumReg,rationalDenReg,rationalCeilReg,t3,t5,t6,tauReg,vJ] ++
  [rationalNumReg,rationalDenReg,rationalCeilReg,SQX,SQS,SQF,SQT,SQU,pU,vJ] ++
  [rationalNumReg,rationalDenReg,GCA,GCB,GCQ,GCR,piNumReg,piDenReg,vJ] ++
  [SQX,SQS,SQF,SQT,SQU,xMaxReg,dStarReg,vJ] ++
  [omegaOneReg,omegaTwoReg,SQX,SQS,SQF,SQT,SQU,mFourierReg,vJ] ++
  [rationalNumReg,rationalDenReg,GCA,GCB,GCQ,GCR,etaNumReg,etaDenReg,vJ] ++
  [rationalNumReg,rationalDenReg,rationalCeilReg,t3,t5,t6,qExponentReg,vJ] ++
  [P2E,P2X,P2I,qReg,pX1,ellFieldReg,seedLengthReg,vJ]

/-- The full work of the early public rules of `sec:params`,
paper/paper.tex, counts every integer loop and
both canonical rational reductions. -/
def publicScalesCost (x : Cells.ParameterInput) (p : Cells.Parameters) (num den : ℕ) : ℕ :=
  (10*x.n*(x.n+1)+15*x.n+251) + concentrationCost p.m p.k p.Jmax x.beta +
    tauCost x.beta + (20*uRootArgument x.n p.r x.W num den+20000) +
    (14*(Nat.size p.tau+Nat.size (4*p.U))+100) +
    (20*xMaxArgument x.n p.r p.tau+158) +
    (20*fourierTheta p.m x.G1 x.G2+160) +
    (14*(Nat.size num+Nat.size (16*p.MF*den))+120) +
    (30*p.Qexp+20100) + 8

/-- Executing the full early rules of `sec:params`,
paper/paper.tex, produces their exact complete
public record before any later degree, prime or chain success.
All resource premises describe concrete operands of the executed
integer programs. -/
theorem publicScalesProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (x : Cells.ParameterInput) (p : Cells.Parameters) (hs : Cells.CoreRules x p)
    (num den : ℕ) (hbn : x.beta.num = num) (hbd : x.beta.den = den)
    (hnv : a.env vN = x.n) (hrv : a.env rReg = p.r) (hmv : a.env mReg = p.m)
    (hJv : a.env pJM = p.Jmax) (hWv : a.env pW = x.W)
    (hnumv : a.env vNUM = num) (hdenv : a.env vDEN = den)
    (hG1v : a.env vG1 = x.G1) (hG2v : a.env vG2 = x.G2)
    (hrpos : 0 < p.r) (htau : 0 < p.tau) (hUpos : 0 < p.U)
    (hnumpos : 0 < num)
    (hdims : x.n*(x.n+1)+2*x.n+32 ≤ C.Wd)
    (hcwidth : concentrationExponent p.m p.k < C.Wd)
    (hcleft : 4*p.Jmax*2^concentrationExponent p.m p.k*den < 2^C.Wd)
    (hcbound : 2^TBound (concentrationExponent p.m p.k) p.Jmax x.beta*num < 2^C.Wd)
    (hcbits : TBound (concentrationExponent p.m p.k) p.Jmax x.beta+2 < C.Wd)
    (htauW : p.k+32*den+4*num+16 < 2^C.Wd)
    (huratio : uNumerator p.r x.W den+2*uDenominator x.n num+4 < 2^C.Wd)
    (huroot : uRootArgument x.n p.r x.W num den*uRootArgument x.n p.r x.W num den+
      uRootArgument x.n p.r x.W num den+3 < 2^C.Wd)
    (hpiW : 2*(p.tau+4*p.U)+4 < 2^C.Wd)
    (hxroot : xMaxArgument x.n p.r p.tau*xMaxArgument x.n p.r p.tau+
      xMaxArgument x.n p.r p.tau+3 < 2^C.Wd)
    (hxcut : 2*p.Xmax*p.U+6*p.r*p.tau+16 < 2^C.Wd)
    (hfourier : fourierTheta p.m x.G1 x.G2*fourierTheta p.m x.G1 x.G2+
      fourierTheta p.m x.G1 x.G2+4*p.m+16 < 2^C.Wd)
    (hetaW : 2*(num+16*p.MF*den)+4 < 2^C.Wd)
    (hsample : 16*(sampleNumerator p.N p.m (p.omega1*p.omega2) p.eta.den+
      sampleDenominator p.eta.num.natAbs)+256 < 2^C.Wd)
    (hQexp : p.Qexp < C.Wd)
    (hseed : 2*p.m*max p.k (p.Qexp+1)+p.k+p.Qexp+32 < 2^C.Wd) :
    Hs C publicScalesProgram a (publicScalesCost x p num den) (fun b =>
      RegisterValues b (publicScaleValues p) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      b.out=a.out ∧ Cst b ∧ FrS a b publicScalesT) := by
  have hnpos := hs.n_pos
  have hWpos : 0 < x.W := hs.input_valid.2.1
  have hdenpos : 0 < den := by rw [← hbd]; exact x.beta.den_pos
  have hmpos : 0 < p.m := by rw [hs.m_eq]; norm_num
  have hJpos : 1 ≤ p.Jmax := by rw [hs.Jmax_eq]; omega
  have hbetaUpper : x.beta ≤ 1/16 := hs.input_valid.2.2.2.2.2.1
  have hrle : p.r ≤ x.n := by have := hs.r_bound; omega
  have hNpos : 0 < p.N := by rw [hs.N_eq]; positivity
  have hEtaNum : p.eta.num = (p.eta.num.natAbs : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_pos (Rat.num_pos.mpr hs.eta_pos)]
  have hEtaNumPos : 0 < p.eta.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr hs.eta_pos).ne'
  have hpi : p.pi0 = (p.tau:ℚ)/(4*p.U:ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.pi0_eq
  have heta : p.eta = x.beta/(16*p.MF:ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.eta_eq
  unfold publicScalesProgram
  have in1_n : a.env vN = x.n := by
    exact hnv
  have in1_r : a.env rReg = p.r := by
    exact hrv
  refine Hx.hs (Hs.then (dimensionsStage_spec C a hc x.n p.r in1_n in1_r hrpos hrle hdims)
    (fun s1 ⟨raw_s, raw_b, raw_k, raw_N, cp1, wq1, out1, c1, f1⟩ n1 hn1 => ?_))
  have v1_s : s1.env sReg = p.s := by simpa only [hs.s_eq] using raw_s
  have v1_b : s1.env bReg = p.b := by simpa only [hs.b_eq, hs.s_eq] using raw_b
  have v1_k : s1.env pK = p.k := by simpa only [hs.k_eq, hs.s_eq] using raw_k
  have v1_N : s1.env nSideReg = p.N := by simpa only [hs.N_eq, hs.k_eq, hs.s_eq] using raw_N
  have in2_m : s1.env mReg = p.m := by
    simp (disch := decide) only [f1.ev]
    exact hmv
  have in2_k : s1.env pK = p.k := by
    exact v1_k
  have in2_J : s1.env pJM = p.Jmax := by
    simp (disch := decide) only [f1.ev]
    exact hJv
  have in2_num : s1.env vNUM = num := by
    simp (disch := decide) only [f1.ev]
    exact hnumv
  have in2_den : s1.env vDEN = den := by
    simp (disch := decide) only [f1.ev]
    exact hdenv
  refine Hs.then (concentrationProgram_spec C s1 c1 p.m p.k p.Jmax num den x.beta in2_m in2_k in2_J in2_num in2_den hbn hbd hs.beta_pos hbetaUpper hJpos hcwidth hcleft hcbound hcbits)
    (fun s2 ⟨raw_T, raw_restorek, cp2, wq2, out2, c2, f2⟩ n2 hn2 => ?_)
  have v2_T : s2.env pT = p.T := by simpa only [hs.T_eq] using raw_T
  have v2_k : s2.env pK = p.k := raw_restorek
  have in3_k : s2.env pK = p.k := by
    exact v2_k
  have in3_num : s2.env vNUM = num := by
    simp (disch := decide) only [f2.ev, f1.ev]
    exact hnumv
  have in3_den : s2.env vDEN = den := by
    simp (disch := decide) only [f2.ev, f1.ev]
    exact hdenv
  refine Hs.then (tauProgram_spec C s2 c2 p.k num den x.beta in3_k in3_num in3_den hbn hbd hnumpos htauW)
    (fun s3 ⟨raw_tau, cp3, wq3, out3, c3, f3⟩ n3 hn3 => ?_)
  have v3_tau : s3.env tauReg = p.tau := by simpa only [hs.tau_eq] using raw_tau
  have in4_n : s3.env vN = x.n := by
    simp (disch := decide) only [f3.ev, f2.ev, f1.ev]
    exact hnv
  have in4_r : s3.env rReg = p.r := by
    simp (disch := decide) only [f3.ev, f2.ev, f1.ev]
    exact hrv
  have in4_W : s3.env pW = x.W := by
    simp (disch := decide) only [f3.ev, f2.ev, f1.ev]
    exact hWv
  have in4_num : s3.env vNUM = num := by
    simp (disch := decide) only [f3.ev, f2.ev, f1.ev]
    exact hnumv
  have in4_den : s3.env vDEN = den := by
    simp (disch := decide) only [f3.ev, f2.ev, f1.ev]
    exact hdenv
  have in4_tau : s3.env tauReg = p.tau := by
    exact v3_tau
  refine Hs.then (uProgram_spec C s3 c3 x.n p.r x.W num den p.tau x.beta in4_n in4_r in4_W in4_num in4_den in4_tau hbn hbd hnpos hrpos hWpos hnumpos hdenpos huratio huroot)
    (fun s4 ⟨raw_U, cp4, wq4, out4, c4, f4⟩ n4 hn4 => ?_)
  have v4_U : s4.env pU = p.U := by simpa only [hs.U_eq] using raw_U
  have in5_tau : s4.env tauReg = p.tau := by
    simp (disch := decide) only [f4.ev]
    exact v3_tau
  have in5_U : s4.env pU = p.U := by
    exact v4_U
  refine Hs.then (piProgram_spec C s4 c4 p.tau p.U in5_tau in5_U hUpos hpiW)
    (fun s5 ⟨raw_piN, raw_piD, cp5, wq5, out5, c5, f5⟩ n5 hn5 => ?_)
  have v5_piN : s5.env piNumReg = p.pi0.num.natAbs := by simpa only [← hpi] using raw_piN
  have v5_piD : s5.env piDenReg = p.pi0.den := by simpa only [← hpi] using raw_piD
  have in6_n : s5.env vN = x.n := by
    simp (disch := decide) only [f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hnv
  have in6_r : s5.env rReg = p.r := by
    simp (disch := decide) only [f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hrv
  have in6_tau : s5.env tauReg = p.tau := by
    simp (disch := decide) only [f5.ev, f4.ev]
    exact v3_tau
  have in6_U : s5.env pU = p.U := by
    simp (disch := decide) only [f5.ev]
    exact v4_U
  refine Hs.then (populationStage_spec C s5 c5 x.n p.r p.tau p.U in6_n in6_r in6_tau in6_U hnpos hrpos htau hUpos hxroot (by simpa only [← hs.Xmax_eq] using hxcut))
    (fun s6 ⟨raw_X, raw_d, cp6, wq6, out6, c6, f6⟩ n6 hn6 => ?_)
  have v6_X : s6.env xMaxReg = p.Xmax := by simpa only [hs.Xmax_eq] using raw_X
  have v6_d : s6.env dStarReg = p.dstar := by simpa only [hs.dstar_eq, hs.Xmax_eq] using raw_d
  have in7_m : s6.env mReg = p.m := by
    simp (disch := decide) only [f6.ev, f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hmv
  have in7_G1 : s6.env vG1 = x.G1 := by
    simp (disch := decide) only [f6.ev, f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hG1v
  have in7_G2 : s6.env vG2 = x.G2 := by
    simp (disch := decide) only [f6.ev, f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hG2v
  refine Hs.then (fourierSizesProgram_spec C s6 c6 p.m x.G1 x.G2 in7_m in7_G1 in7_G2 hfourier)
    (fun s7 ⟨raw_o1, raw_o2, raw_MF, cp7, wq7, out7, c7, f7⟩ n7 hn7 => ?_)
  have v7_o1 : s7.env omegaOneReg = p.omega1 := by simpa only [hs.omega1_eq] using raw_o1
  have v7_o2 : s7.env omegaTwoReg = p.omega2 := by simpa only [hs.omega2_eq] using raw_o2
  have v7_MF : s7.env mFourierReg = p.MF := by simpa only [hs.MF_eq, hs.omega1_eq, hs.omega2_eq, fourierTheta] using raw_MF
  have in8_num : s7.env vNUM = num := by
    simp (disch := decide) only [f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hnumv
  have in8_den : s7.env vDEN = den := by
    simp (disch := decide) only [f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hdenv
  have in8_MF : s7.env mFourierReg = p.MF := by
    exact v7_MF
  refine Hs.then (etaProgram_spec C s7 c7 num den p.MF x.beta in8_num in8_den in8_MF hbn hbd hdenpos hs.MF_pos hetaW)
    (fun s8 ⟨raw_etaN, raw_etaD, cp8, wq8, out8, c8, f8⟩ n8 hn8 => ?_)
  have v8_etaN : s8.env etaNumReg = p.eta.num.natAbs := by simpa only [← heta] using raw_etaN
  have v8_etaD : s8.env etaDenReg = p.eta.den := by simpa only [← heta] using raw_etaD
  have in9_N : s8.env nSideReg = p.N := by
    simp (disch := decide) only [f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
    exact v1_N
  have in9_m : s8.env mReg = p.m := by
    simp (disch := decide) only [f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev, f1.ev]
    exact hmv
  have in9_o1 : s8.env omegaOneReg = p.omega1 := by
    simp (disch := decide) only [f8.ev]
    exact v7_o1
  have in9_o2 : s8.env omegaTwoReg = p.omega2 := by
    simp (disch := decide) only [f8.ev]
    exact v7_o2
  have in9_etaN : s8.env etaNumReg = p.eta.num.natAbs := by
    exact v8_etaN
  have in9_etaD : s8.env etaDenReg = p.eta.den := by
    exact v8_etaD
  have in9_k : s8.env pK = p.k := by
    simp (disch := decide) only [f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
    exact v2_k
  refine Hs.last (samplingStage_spec C s8 c8 p.N p.m p.omega1 p.omega2 p.eta.num.natAbs p.eta.den p.k p.eta in9_N in9_m in9_o1 in9_o2 in9_etaN in9_etaD in9_k hEtaNum rfl hNpos hmpos hs.omega_pos.1 hs.omega_pos.2 hEtaNumPos p.eta.den_pos hsample (by simpa only [← hs.Qexp_eq] using hQexp) (by simpa only [← hs.Qexp_eq] using hseed))
    (fun s9 ⟨raw_e, raw_Q, raw_ell, raw_S, cp9, wq9, out9, c9, f9⟩ n9 hn9 => ?_)
  have v9_e : s9.env qExponentReg = p.Qexp := by simpa only [hs.Qexp_eq] using raw_e
  have v9_Q : s9.env qReg = p.Q := by simpa only [hs.Q_eq, hs.Qexp_eq] using raw_Q
  have v9_ell : s9.env ellFieldReg = p.ellf := by simpa only [hs.ellf_eq, hs.Qexp_eq] using raw_ell
  have v9_S : s9.env seedLengthReg = p.S := by simpa only [hs.S_eq, hs.ellf_eq, hs.Qexp_eq] using raw_S
  refine ⟨⟨?_, ?_, ?_, ?_, c9, ?_⟩, ?_⟩
  · simp only [RegisterValues, publicScaleValues, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_s
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_b
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_k
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev, f2.ev]
      exact v1_N
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev, f3.ev]
      exact v2_T
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev, f4.ev]
      exact v3_tau
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev, f5.ev]
      exact v4_U
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev]
      exact v5_piN
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev, f6.ev]
      exact v5_piD
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev]
      exact v6_X
    · simp (disch := decide) only [f9.ev, f8.ev, f7.ev]
      exact v6_d
    · simp (disch := decide) only [f9.ev, f8.ev]
      exact v7_o1
    · simp (disch := decide) only [f9.ev, f8.ev]
      exact v7_o2
    · simp (disch := decide) only [f9.ev, f8.ev]
      exact v7_MF
    · simp (disch := decide) only [f9.ev]
      exact v8_etaN
    · simp (disch := decide) only [f9.ev]
      exact v8_etaD
    · exact v9_e
    · exact v9_Q
    · exact v9_ell
    · rintro y rfl
      exact v9_S
  · rw [cp9, cp8, cp7, cp6, cp5, cp4, cp3, cp2, cp1]
  · rw [wq9, wq8, wq7, wq6, wq5, wq4, wq3, wq2, wq1]
  · rw [out9, out8, out7, out6, out5, out4, out3, out2, out1]
  · exact FrS.trans (FrS.weaken f1 (by decide)) (FrS.trans (FrS.weaken f2 (by decide)) (FrS.trans (FrS.weaken f3 (by decide)) (FrS.trans (FrS.weaken f4 (by decide)) (FrS.trans (FrS.weaken f5 (by decide)) (FrS.trans (FrS.weaken f6 (by decide)) (FrS.trans (FrS.weaken f7 (by decide)) (FrS.trans (FrS.weaken f8 (by decide)) (FrS.weaken f9 (by decide)))))))))
  · unfold publicScalesCost
    rw [← hs.Qexp_eq] at hn9
    omega

end NearQuarticWires.StagePrep
