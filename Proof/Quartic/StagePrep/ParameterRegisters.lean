import Proof.Gates.Dispatch.ParamsA

/-!
# Registers for the exact public parameter computation

Paper: `sec:params`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- `m`, `sec:params`, paper/paper.tex. -/
def mReg : Fin VV := ⟨67, by decide⟩
/-- `r`, `sec:params`, paper/paper.tex. -/
def rReg : Fin VV := ⟨68, by decide⟩
/-- `s`, `sec:params`, paper/paper.tex. -/
def sReg : Fin VV := ⟨69, by decide⟩
/-- `b`, `sec:params`, paper/paper.tex. -/
def bReg : Fin VV := ⟨70, by decide⟩
/-- `N`, `sec:params`, paper/paper.tex. -/
def nSideReg : Fin VV := ⟨71, by decide⟩
/-- `tau`, `sec:params`, paper/paper.tex. -/
def tauReg : Fin VV := ⟨72, by decide⟩
/-- `Xmax`, `sec:params`, paper/paper.tex. -/
def xMaxReg : Fin VV := ⟨73, by decide⟩
/-- `dstar`, `sec:params`, paper/paper.tex. -/
def dStarReg : Fin VV := ⟨74, by decide⟩
/-- `omega1`, `sec:params`, paper/paper.tex. -/
def omegaOneReg : Fin VV := ⟨75, by decide⟩
/-- `omega2`, `sec:params`, paper/paper.tex. -/
def omegaTwoReg : Fin VV := ⟨76, by decide⟩
/-- `MF`, `sec:params`, paper/paper.tex. -/
def mFourierReg : Fin VV := ⟨77, by decide⟩
/-- `Q`, `sec:params`, paper/paper.tex. -/
def qReg : Fin VV := ⟨78, by decide⟩
/-- `ellf`, `sec:params`, paper/paper.tex. -/
def ellFieldReg : Fin VV := ⟨79, by decide⟩
/-- `S`, `sec:params`, paper/paper.tex. -/
def seedLengthReg : Fin VV := ⟨80, by decide⟩
/-- The atom count, `sec:params`, paper/paper.tex. -/
def atomsReg : Fin VV := ⟨81, by decide⟩
/-- The child cap, `sec:params`, paper/paper.tex. -/
def childCapReg : Fin VV := ⟨82, by decide⟩
/-- `Uocc`, `sec:params`, paper/paper.tex. -/
def occurrenceCapReg : Fin VV := ⟨83, by decide⟩
/-- `BN`, `sec:params`, paper/paper.tex. -/
def coefficientBitsReg : Fin VV := ⟨84, by decide⟩
/-- The numerator of `pi0`, `sec:params`, paper/paper.tex. -/
def piNumReg : Fin VV := ⟨85, by decide⟩
/-- The denominator of `pi0`, `sec:params`, paper/paper.tex. -/
def piDenReg : Fin VV := ⟨86, by decide⟩
/-- The numerator of `eta`, `sec:params`, paper/paper.tex. -/
def etaNumReg : Fin VV := ⟨87, by decide⟩
/-- The denominator of `eta`, `sec:params`, paper/paper.tex. -/
def etaDenReg : Fin VV := ⟨88, by decide⟩
/-- The exponent of `Q`, `sec:params`, paper/paper.tex. -/
def qExponentReg : Fin VV := ⟨89, by decide⟩
/-- `ell0`, `sec:params`, paper/paper.tex. -/
def ellZeroReg : Fin VV := ⟨90, by decide⟩

end NearQuarticWires.StagePrep
