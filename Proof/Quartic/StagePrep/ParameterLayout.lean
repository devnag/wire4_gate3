import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.Program.Stages
import Proof.Gates.Dispatch.PrintP

/-!
# The complete parameter word layout

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- The fixed scalar prefix of the exact record in
`sec:params`, paper/paper.tex. The three entries
for each rational are its sign, numerator and denominator. -/
def parameterHeadRegisters : List (Fin VV) :=
  [pLAM, pMU, mReg, rReg, sReg, bReg, pK, nSideReg, pJM, pT,
    tauReg, pU, xMaxReg, dStarReg, omegaOneReg, omegaTwoReg, mFourierReg,
    qReg, ellFieldReg, seedLengthReg, atomsReg, childCapReg, occurrenceCapReg,
    pDM, coefficientBitsReg, pP, pE, pHE, pH, pLW,
    vZ, piNumReg, piDenReg, vZ, etaNumReg, etaDenReg, qExponentReg, pNP]

/-- The scalar suffix preceding the factor payload of
`sec:params`, paper/paper.tex. The final entry
is the length of the actual factor list. -/
def parameterTailRegisters : List (Fin VV) :=
  [pWIN, pL2, pM1, pJ, pA, pLB, vZ, ellZeroReg, v1, pCI]

/-- The word before the prime payload in `sec:params`,
paper/paper.tex. -/
def parameterHeadWord (p : Cells.Parameters) : List Bool :=
  natWord p.lambda ++ natWord p.mu ++ natWord p.m ++ natWord p.r ++ natWord p.s ++ natWord p.b ++
    natWord p.k ++ natWord p.N ++ natWord p.Jmax ++ natWord p.T ++ natWord p.tau ++ natWord p.U ++
    natWord p.Xmax ++ natWord p.dstar ++ natWord p.omega1 ++ natWord p.omega2 ++ natWord p.MF ++
    natWord p.Q ++ natWord p.ellf ++ natWord p.S ++ natWord p.NatAtoms ++ natWord p.childCap ++
    natWord p.Uocc ++ natWord p.Dmax ++ natWord p.BN ++ natWord p.P ++ natWord p.e ++ natWord p.hE ++
    natWord p.h ++ natWord p.Lw ++ ratWord p.pi0 ++ ratWord p.eta ++ natWord p.Qexp ++
    natWord p.primes.card

/-- The word after the prime payload in `sec:params`,
paper/paper.tex. -/
def parameterTailWord (p : Cells.Parameters) : List Bool :=
  natWord p.Dprime ++ natWord p.L2 ++ natWord p.M1 ++ natWord p.J ++ natWord p.A ++
    natWord p.Lambda ++ ratWord p.ell0 ++ natWord p.factors.length

/-- The complete record of `sec:params`, paper/paper.tex, contains every scalar, prime and factor field
in exactly the public stage codec order. -/
theorem parametersWord_layout (p : Cells.Parameters) :
    Program.parametersWord p = parameterHeadWord p ++
      (p.primes.sort (· ≤ ·)).flatMap natWord ++ parameterTailWord p ++
      p.factors.flatMap natWord := by
  simp only [Program.parametersWord, parameterHeadWord, parameterTailWord,
    listWord, Finset.length_sort, List.append_assoc]

/-- Every scalar register of `sec:params`, paper/paper.tex, is outside the scratch registers of the binary
word emitter. -/
theorem parameter_registers_printable :
    (∀ x ∈ parameterHeadRegisters, x.val < 200 ∧ x ∉ pvT) ∧
    (∀ x ∈ parameterTailRegisters, x.val < 200 ∧ x ∉ pvT) := by
  decide

end NearQuarticWires.StagePrep
