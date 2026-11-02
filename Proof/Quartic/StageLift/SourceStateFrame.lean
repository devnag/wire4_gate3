import Proof.Quartic.StageLift.SourceLoopState

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells

/-- Step 3 and `lem:print`, paper/paper.tex: actual source headers retained through every generated
walk, independently of phase-local arithmetic scratch. -/
def sourceHeaderRegisters : List (Fin VV) :=
  [preparedLength, degreeVar, printArityVar, degreeExponent, degreeChain,
    StageRecovery.modulusVar, degreePrime, signCodeVar, callKindVar, printWalkCount]

/-- Step 3, `sec:algorithm`, paper/paper.tex: source writers may
change phase-local cursors and callee replies while retaining all real
original data and the two live preparation/Gamma cursor positions. -/
theorem WalkSourceState.of_frame {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {cursor next : ℕ} {a b : DS VV MM} (ha : WalkSourceState C r cursor a)
    (hram : b.ram = a.ram)
    (hfields : ∀ x ∈ sourceHeaderRegisters, b.env x = a.env x)
    (hgamma : b.rc gammaStore = gammaByteCursor r next)
    (hprep : b.rc preparedStore = a.rc preparedStore)
    (hc : Cst b) (hv : Valid C b) (hkin : b.kin = []) : WalkSourceState C r next b := by
  have hs := ha.sources
  refine ⟨?_, hgamma, hc, source_valid_set hv printWalkIndex 0 (Nat.two_pow_pos _), hkin⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrFun hram callStore).trans hs.originalCall
  · exact (congrFun hram parameterStore).trans hs.scalarFields
  · exact (congrFun hram primeStore).trans hs.primeFields
  · exact (congrFun hram factorStore).trans hs.factorFields
  · exact (congrFun hram witnessStore).trans hs.witnessBits
  · exact (congrFun hram gammaStore).trans hs.gammaBits
  · exact (congrFun hram indexStore).trans hs.indexFields
  · exact (congrFun hram preparedStore).trans hs.preparedBits
  · exact (hfields _ (by decide)).trans hs.preparedBytes
  · exact (hfields _ (by decide)).trans hs.degree
  · exact (hfields _ (by decide)).trans hs.arity
  · exact (hfields _ (by decide)).trans hs.exponent
  · exact (hfields _ (by decide)).trans hs.chains
  · exact (hfields _ (by decide)).trans hs.modulus
  · exact (hfields _ (by decide)).trans hs.prime
  · exact (hfields _ (by decide)).trans hs.signs
  · exact (hfields _ (by decide)).trans hs.kind
  · simp only [sourceEntryView, Function.update_self]
  · exact (hfields _ (by decide)).trans hs.walkCount
  · simp only [sourceEntryView, Function.update_self]
  · exact hprep.trans hs.preparedCursor

end NearQuarticWires.StageLift
