import Proof.Foundations.OperationalWilliamsSourceCore
import Proof.Foundations.ExecutableProgramTightRefuterSource
import Proof.Foundations.TrustExactDecompositionChildCount

/-!
# Published theorem assumptions

The eight fields are the unique published-source firewall.  Algorithmic
sources carry executable refinements whose outputs and resource charges come
from fixed interpreters or literal local-machine receipts.  Genuinely
mathematical sources remain semantic.  No algorithmic row stores an
independent semantic duplicate.
-/

namespace NearCubicWires

open SourceInterfaces
open ExecutableInterfaces
open ExecutableProgramTimedSource
open ExecutableProgramTightRefuterSource
open WilliamsPublishedForm

structure PublishedContracts where
  thresholdNormalization : ThresholdNormalizationContract
  /-- The decomposition field assumes an algorithm exists; its child-count
bound is derived from the interpreter rather than stored separately.
The field is `Nonempty ExecutableExactDecompositionAlgorithm`.
`ExecutableInterfaces.executableDisjointExactDecomposition_iff_legacy`
in `Proof/Foundations/TrustExactDecompositionChildCount.lean` proves equivalence with the older
two-clause contract. No sharper output-sensitive decomposition bound
is needed by this interface. 













-/
  disjointExactDecomposition : ExecutableDisjointExactDecompositionContract
  booleanRectangularProduct : FaithfulWilliamsRectangularProductContract
  expanderSpectrum : ExpanderSpectrumContract
  primeThetaBound : PrimeThetaBoundContract
  projectionPcpAndPcpp : ExecutableProgramProjectionPcpAndPcppContract
  refuterAndXor : CertifiedTightExecutableProgramRefuterAndXorContract
  worstCaseAmplifier : ExecutableWorstCaseAmplifierContract

theorem PublishedContracts.disjointExactDecompositionSemantic
    (contracts : PublishedContracts) :
    DisjointExactDecompositionContract :=
  executableDisjointDecomposition_implies_semantic
    contracts.disjointExactDecomposition

theorem PublishedContracts.booleanRectangularProductSemantic
    (contracts : PublishedContracts) :
    BooleanRectangularProductContract :=
  faithfulWilliams_implies_semantic contracts.booleanRectangularProduct

theorem PublishedContracts.pointwisePcppExecutable
    (contracts : PublishedContracts) :
    ExecutablePointwisePCPPContract :=
  contracts.projectionPcpAndPcpp.2

/-- Safe compatibility for the existing refuter recovery cone.  The hierarchy
timed machine remains definitionally derived from the selected executable
program; no arbitrary acceptance/step pair enters through this projection. -/
theorem PublishedContracts.refuterAndXorLegacy
    (contracts : PublishedContracts) :
    ExecutableRefuterAndXorContract :=
  certifiedTightProgramRefuterAndXor_implies_legacy contracts.refuterAndXor

theorem PublishedContracts.worstCaseAmplifierSemantic
    (contracts : PublishedContracts) :
    WorstCaseAmplifierContract :=
  executableWorstCaseAmplifier_implies_semantic contracts.worstCaseAmplifier

theorem PublishedContracts.asPublishedConjunction
    (contracts : PublishedContracts) :
    ThresholdNormalizationContract ∧
      ExecutableDisjointExactDecompositionContract ∧
      FaithfulWilliamsRectangularProductContract ∧
      ExpanderSpectrumContract ∧
      PrimeThetaBoundContract ∧
      ExecutableProgramProjectionPcpAndPcppContract ∧
      CertifiedTightExecutableProgramRefuterAndXorContract ∧
      ExecutableWorstCaseAmplifierContract :=
  ⟨contracts.thresholdNormalization,
    contracts.disjointExactDecomposition,
    contracts.booleanRectangularProduct,
    contracts.expanderSpectrum,
    contracts.primeThetaBound,
    contracts.projectionPcpAndPcpp,
    contracts.refuterAndXor,
    contracts.worstCaseAmplifier⟩

end NearCubicWires
