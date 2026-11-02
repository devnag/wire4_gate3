import Proof.Quartic.StagePrep.ParameterLayout
import Proof.Quartic.StagePrep.RegisterValues

/-!
# Complete parameter memory and the public codec

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires.RepairRepresentation

/-- The complete scalar memory of `sec:params`,
paper/paper.tex, includes every record field,
prime count and factor-list length used by the physical writer. -/
def parameterMemoryValues (p : Cells.Parameters) : List (Fin VV × ℕ) :=
  [(pLAM,p.lambda),
    (pMU,p.mu),
    (mReg,p.m),
    (rReg,p.r),
    (sReg,p.s),
    (bReg,p.b),
    (pK,p.k),
    (nSideReg,p.N),
    (pJM,p.Jmax),
    (pT,p.T),
    (tauReg,p.tau),
    (pU,p.U),
    (xMaxReg,p.Xmax),
    (dStarReg,p.dstar),
    (omegaOneReg,p.omega1),
    (omegaTwoReg,p.omega2),
    (mFourierReg,p.MF),
    (qReg,p.Q),
    (ellFieldReg,p.ellf),
    (seedLengthReg,p.S),
    (atomsReg,p.NatAtoms),
    (childCapReg,p.childCap),
    (occurrenceCapReg,p.Uocc),
    (pDM,p.Dmax),
    (coefficientBitsReg,p.BN),
    (pP,p.P),
    (pE,p.e),
    (pHE,p.hE),
    (pH,p.h),
    (pLW,p.Lw),
    (piNumReg,p.pi0.num.natAbs),
    (piDenReg,p.pi0.den),
    (etaNumReg,p.eta.num.natAbs),
    (etaDenReg,p.eta.den),
    (qExponentReg,p.Qexp),
    (pNP,p.primes.card),
    (pWIN,p.Dprime),
    (pL2,p.L2),
    (pM1,p.M1),
    (pJ,p.J),
    (pA,p.A),
    (pLB,p.Lambda),
    (ellZeroReg,p.ell0.num.natAbs),
    (pCI,p.factors.length)]

/-- Exact stored fields in `sec:params`, paper/paper.tex, determine both literal scalar words, including
all three rational signs and the integer chain scale. -/
theorem parameterMemory_layout (a : DS VV) (hc : Cst a) (p : Cells.Parameters)
    (h : RegisterValues a (parameterMemoryValues p))
    (hpi : 0 ≤ p.pi0) (heta : 0 ≤ p.eta) (hell : 0 ≤ p.ell0)
    (hden : p.ell0.den=1) :
    parameterHeadRegisters.flatMap (fun v => natWord (a.env v))=parameterHeadWord p ∧
    parameterTailRegisters.flatMap (fun v => natWord (a.env v))=parameterTailWord p := by
  have v0 : a.env pLAM=p.lambda := h (pLAM,p.lambda) (by simp [parameterMemoryValues])
  have v1 : a.env pMU=p.mu := h (pMU,p.mu) (by simp [parameterMemoryValues])
  have v2 : a.env mReg=p.m := h (mReg,p.m) (by simp [parameterMemoryValues])
  have v3 : a.env rReg=p.r := h (rReg,p.r) (by simp [parameterMemoryValues])
  have v4 : a.env sReg=p.s := h (sReg,p.s) (by simp [parameterMemoryValues])
  have v5 : a.env bReg=p.b := h (bReg,p.b) (by simp [parameterMemoryValues])
  have v6 : a.env pK=p.k := h (pK,p.k) (by simp [parameterMemoryValues])
  have v7 : a.env nSideReg=p.N := h (nSideReg,p.N) (by simp [parameterMemoryValues])
  have v8 : a.env pJM=p.Jmax := h (pJM,p.Jmax) (by simp [parameterMemoryValues])
  have v9 : a.env pT=p.T := h (pT,p.T) (by simp [parameterMemoryValues])
  have v10 : a.env tauReg=p.tau := h (tauReg,p.tau) (by simp [parameterMemoryValues])
  have v11 : a.env pU=p.U := h (pU,p.U) (by simp [parameterMemoryValues])
  have v12 : a.env xMaxReg=p.Xmax := h (xMaxReg,p.Xmax) (by simp [parameterMemoryValues])
  have v13 : a.env dStarReg=p.dstar := h (dStarReg,p.dstar) (by simp [parameterMemoryValues])
  have v14 : a.env omegaOneReg=p.omega1 := h (omegaOneReg,p.omega1) (by simp [parameterMemoryValues])
  have v15 : a.env omegaTwoReg=p.omega2 := h (omegaTwoReg,p.omega2) (by simp [parameterMemoryValues])
  have v16 : a.env mFourierReg=p.MF := h (mFourierReg,p.MF) (by simp [parameterMemoryValues])
  have v17 : a.env qReg=p.Q := h (qReg,p.Q) (by simp [parameterMemoryValues])
  have v18 : a.env ellFieldReg=p.ellf := h (ellFieldReg,p.ellf) (by simp [parameterMemoryValues])
  have v19 : a.env seedLengthReg=p.S := h (seedLengthReg,p.S) (by simp [parameterMemoryValues])
  have v20 : a.env atomsReg=p.NatAtoms := h (atomsReg,p.NatAtoms) (by simp [parameterMemoryValues])
  have v21 : a.env childCapReg=p.childCap := h (childCapReg,p.childCap) (by simp [parameterMemoryValues])
  have v22 : a.env occurrenceCapReg=p.Uocc := h (occurrenceCapReg,p.Uocc) (by simp [parameterMemoryValues])
  have v23 : a.env pDM=p.Dmax := h (pDM,p.Dmax) (by simp [parameterMemoryValues])
  have v24 : a.env coefficientBitsReg=p.BN := h (coefficientBitsReg,p.BN) (by simp [parameterMemoryValues])
  have v25 : a.env pP=p.P := h (pP,p.P) (by simp [parameterMemoryValues])
  have v26 : a.env pE=p.e := h (pE,p.e) (by simp [parameterMemoryValues])
  have v27 : a.env pHE=p.hE := h (pHE,p.hE) (by simp [parameterMemoryValues])
  have v28 : a.env pH=p.h := h (pH,p.h) (by simp [parameterMemoryValues])
  have v29 : a.env pLW=p.Lw := h (pLW,p.Lw) (by simp [parameterMemoryValues])
  have v30 : a.env piNumReg=p.pi0.num.natAbs := h (piNumReg,p.pi0.num.natAbs) (by simp [parameterMemoryValues])
  have v31 : a.env piDenReg=p.pi0.den := h (piDenReg,p.pi0.den) (by simp [parameterMemoryValues])
  have v32 : a.env etaNumReg=p.eta.num.natAbs := h (etaNumReg,p.eta.num.natAbs) (by simp [parameterMemoryValues])
  have v33 : a.env etaDenReg=p.eta.den := h (etaDenReg,p.eta.den) (by simp [parameterMemoryValues])
  have v34 : a.env qExponentReg=p.Qexp := h (qExponentReg,p.Qexp) (by simp [parameterMemoryValues])
  have v35 : a.env pNP=p.primes.card := h (pNP,p.primes.card) (by simp [parameterMemoryValues])
  have v36 : a.env pWIN=p.Dprime := h (pWIN,p.Dprime) (by simp [parameterMemoryValues])
  have v37 : a.env pL2=p.L2 := h (pL2,p.L2) (by simp [parameterMemoryValues])
  have v38 : a.env pM1=p.M1 := h (pM1,p.M1) (by simp [parameterMemoryValues])
  have v39 : a.env pJ=p.J := h (pJ,p.J) (by simp [parameterMemoryValues])
  have v40 : a.env pA=p.A := h (pA,p.A) (by simp [parameterMemoryValues])
  have v41 : a.env pLB=p.Lambda := h (pLB,p.Lambda) (by simp [parameterMemoryValues])
  have v42 : a.env ellZeroReg=p.ell0.num.natAbs := h (ellZeroReg,p.ell0.num.natAbs) (by simp [parameterMemoryValues])
  have v43 : a.env pCI=p.factors.length := h (pCI,p.factors.length) (by simp [parameterMemoryValues])
  have hpiN : ¬p.pi0.num<0 := not_lt.mpr (Rat.num_nonneg.mpr hpi)
  have hetaN : ¬p.eta.num<0 := not_lt.mpr (Rat.num_nonneg.mpr heta)
  have hellN : ¬p.ell0.num<0 := not_lt.mpr (Rat.num_nonneg.mpr hell)
  constructor
  · simp only [parameterHeadRegisters,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      parameterHeadWord,ratWord,NearCubicGates.Close.Interfaces.intWord,
      if_neg hpiN,if_neg hetaN,hc.z,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35]
    simp only [List.append_assoc]
  · simp only [parameterTailRegisters,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      parameterTailWord,ratWord,NearCubicGates.Close.Interfaces.intWord,
      if_neg hellN,hden,hc.z,hc.one,v36,v37,v38,v39,v40,v41,v42,v43]
    simp only [List.append_assoc]

end NearQuarticWires.StagePrep
