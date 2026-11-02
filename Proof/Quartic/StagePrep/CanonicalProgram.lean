import Proof.Quartic.StagePrep.FrontPhysical
import Proof.Quartic.StagePrep.ParameterHeader
import Proof.Quartic.StagePrep.StarLog
import Proof.Quartic.StagePrep.StarDimensions
import Proof.Quartic.StagePrep.ConcentrationProgram
import Proof.Quartic.StagePrep.TauProgram
import Proof.Quartic.StagePrep.UProgram
import Proof.Quartic.StagePrep.PiProgram
import Proof.Quartic.StagePrep.XMaxProgram
import Proof.Quartic.StagePrep.DStarProgram
import Proof.Quartic.StagePrep.FourierSizes
import Proof.Quartic.StagePrep.EtaProgram
import Proof.Quartic.StagePrep.SampleProgram
import Proof.Quartic.StagePrep.SeedSizes
import Proof.Quartic.StagePrep.PrintingSizes
import Proof.Quartic.StagePrep.DegreeSearch
import Proof.Quartic.StagePrep.CoefficientBits
import Proof.Quartic.StagePrep.PrimeSearch
import Proof.Quartic.StagePrep.PrimeWindows
import Proof.Quartic.StagePrep.RateChain
import Proof.Quartic.StagePrep.ChainFinish
import Proof.Quartic.StagePrep.CheckedLe
import Proof.Quartic.StagePrep.ParameterWriter
import Proof.Quartic.StagePrep.PrefixLength
import Proof.Quartic.StagePrep.FrameProgram
import Proof.Quartic.StagePrep.ClosedDock
import Proof.Quartic.StagePrep.DefaultOutput
import Proof.Quartic.StagePrep.PublicScalesProgram

/-!
# The concrete preparation instruction sequence

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- A finite sequential instruction list in the preparation
stage of `prop:time`, paper/paper.tex. -/
def preparationSequence : List (St VV) → St VV
  | [] => skipS
  | s :: ss => .seq s (preparationSequence ss)

/-- The initial height guard of `sec:params`,
paper/paper.tex. -/
def preparationHeaderStage : St VV :=
  .seq parameterHeader (checkedLe pX1 vN (mul (lit 4) (var rReg)))

/-- The public scalar computations of `sec:params`,
paper/paper.tex, run before the degree guard. -/
def preparationScalesStage : St VV := publicScalesProgram

/-- The initial printing comparison of `sec:params`,
paper/paper.tex, is checked before searching. -/
def preparationDegreeStage : St VV := preparationSequence
  [printingSizesProgram, degreeLogProgram, .op (.zero pSI),
    degreeTestProgram, needEq pSF v1]

/-- The two literal greatest searches of `sec:params`,
paper/paper.tex, retain their rejection flag. -/
def preparationPrimeStage : St VV := preparationSequence
  [degreeSearchProgram, coefficientBitsProgram, primeSearchProgram, needEq pPF v1]

/-- The final least lift and moment-degree guard of
`sec:params`, paper/paper.tex. -/
def preparationLiftStage : St VV := .seq liftExponentProgram
  (checkedLe pX1 pDM (add (mul (mul (lit 4) (var mReg)) (var xMaxReg))
    (mul (mul (lit 2) (var mReg)) (var pK))))

/-- The nonempty prime-set guard of `sec:params`,
paper/paper.tex, uses the actual prime census. -/
def preparationWindowsStage : St VV :=
  .seq primeWindowsProgram (needLe v1 pNP)

/-- The new integer height and its concentration guard of
`sec:params`, paper/paper.tex. -/
def preparationHeightStage : St VV := .seq chainHeightProgram
  (checkedLe pX1 pH (mul (lit 64) (var pT)))

/-- The actual stopping search and final chain checks of
`sec:params`, paper/paper.tex. -/
def preparationChainStage : St VV := .seq rateChainProgram (needEq pCF v1)

/-- The final parameter guard of `sec:params`,
paper/paper.tex. -/
def preparationFinishStage : St VV := .seq chainFinishProgram (needLe pJ pJM)

/-- Every stage of `sec:params`, paper/paper.tex, is skipped after the first failed public guard. -/
def guardedPreparationStages : List (St VV) → St VV
  | [] => skipS
  | s :: ss => .seq (guard s) (guardedPreparationStages ss)

/-- The concrete canonical parameter computation of
`sec:params`, paper/paper.tex. -/
def canonicalPreparation : St VV := guardedPreparationStages
  [preparationHeaderStage, preparationScalesStage, preparationDegreeStage,
    preparationPrimeStage, preparationLiftStage, preparationWindowsStage,
    preparationHeightStage, preparationChainStage, preparationFinishStage]

/-- The successful preparation payload of `sec:params` and
the witness convention, paper/paper.tex. -/
def successfulPreparationOutput : St VV := preparationSequence
  [.op (.emit true), copyCW, parameterWriter, prefixLengthProgram, prefixReader]

/-- The complete raw preparation instruction sequence of
`prop:time`, paper/paper.tex, has separate
constant, failed-guard and successful dispatch exits. -/
def rawPreparationProgram (B1 B2 : ℕ) : St VV :=
  .seq (preparationFront B1 B2)
    (.ite (.eq vADM v1)
      (.ite (.eq censusTotal vZ) closedZeroOutput
        (.seq canonicalPreparation
          (.ite (.eq vADM v1) successfulPreparationOutput defaultPreparationOutput)))
      defaultPreparationOutput)

/-- The exact outer output-frame instruction sequence of
`thm:counter`, paper/paper.tex, for preparation. -/
def framedPreparationProgram (B1 B2 : ℕ) : St VV :=
  framedProgram (rawPreparationProgram B1 B2)

end NearQuarticWires.StagePrep
