import Proof.Foundations.EncodedListLengthWidthBound
import Proof.Foundations.VerifiedLinker

/-! # Deriving the decomposition child count

`ExecutableDisjointExactDecompositionContract` stores the algorithm;
the former bound

```
∀ request, (algorithm.run request.gate).children.length ≤ algorithm.runner.budget request
```

follows from its fixed runner. The decoded child list is a map of the
encoded spine, `EncodedListLengthWidthBound.encodedListLength_le_natBitLength`
bounds that spine by output width, and `VerifiedLinker.run_output_bounded`
bounds the width by the runner's budget using
`PolynomialNatProgram.run_eq_execute`.

This module also defines
`executableDisjointDecomposition_implies_semantic` in its existing namespace,
since the semantic projection consumes the derived count. 




















-/

namespace NearCubicWires.ExecutableInterfaces

open NearCubicWires
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.EncodedListLengthWidthBound
open NearCubicWires.SourceInterfaces

/-- Spine-length identity at the exact-gate payload type.  Same induction as
`CanonicalEncodedListLengthProgram.encodedListLength_eq_decode`; only the
`Encodable` instance differs. -/
theorem encodedListLength_eq_decode_exactGates (code : ℕ) :
    encodedListLength code =
      ((Encodable.decode code : Option (List (List ℤ × ℤ))).getD []).length := by
  induction code using encodedListLength.induct with
  | case1 =>
      simp [encodedListLength]
  | case2 spine inductionHypothesis =>
      simp [encodedListLength, inductionHypothesis, Nat.add_comm]

/-- `decodeExactThresholdGates` maps over that spine, so it does not move the
length. -/
theorem decodeExactThresholdGates_length (n code : ℕ) :
    (decodeExactThresholdGates n code).length = encodedListLength code := by
  unfold decodeExactThresholdGates
  simp [encodedListLength_eq_decode_exactGates]

/-- **The child count is bounded by the runner's own budget, with no source
assumption.**  This is the clause the published contract used to carry. -/
theorem ExecutableExactDecompositionAlgorithm.children_length_le_budget
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : ExactDecompositionRequest) :
    (algorithm.run request.gate).children.length ≤
      algorithm.runner.budget request := by
  have hchildren :
      (algorithm.run request.gate).children =
        decodeExactThresholdGates request.arity
          (algorithm.runner.execute request) := rfl
  have houtput :
      natBitLength (algorithm.runner.execute request) ≤
        algorithm.runner.budget request :=
    NearCubicWires.VerifiedLinker.run_output_bounded
      (algorithm.runner.run_eq_execute request)
  rw [hchildren, decodeExactThresholdGates_length]
  exact le_trans
    (encodedListLength_le_natBitLength (algorithm.runner.execute request))
    houtput

/-- The decomposition contract is equivalent to the older two-clause
contract: `Nonempty ExecutableExactDecompositionAlgorithm` already implies
the child-count bound through the fixed `NPOracleProgram` interpreter in `StatementSupport.lean`.
The interface needs no independent sharper decomposition estimate. 







-/
theorem executableDisjointExactDecomposition_iff_legacy :
    ExecutableDisjointExactDecompositionContract ↔
      LegacyDisjointExactDecompositionContract := by
  constructor
  · rintro ⟨algorithm⟩
    exact ⟨algorithm,
      ExecutableExactDecompositionAlgorithm.children_length_le_budget algorithm⟩
  · rintro ⟨algorithm, _⟩
    exact ⟨algorithm⟩

/-- Semantic projection of the published decomposition row.  The child-count
and step bounds come from the derivation above rather than from the contract,
at coefficient `algorithm.runner.coefficient` and degree
`algorithm.runner.degree`. -/
theorem executableDisjointDecomposition_implies_semantic :
    ExecutableDisjointExactDecompositionContract →
      DisjointExactDecompositionContract := by
  rintro ⟨algorithm⟩
  refine ⟨algorithm.toSemantic, algorithm.runner.coefficient,
    algorithm.runner.degree, algorithm.runner.coefficientPositive, ?_⟩
  intro n gate
  let request : ExactDecompositionRequest := ⟨n, gate⟩
  refine ⟨le_rfl, ?_⟩
  simpa [ExecutableExactDecompositionAlgorithm.toSemantic,
    ExactDecompositionRequest.measure, PolynomialNatProgram.budget,
    polynomialBudget, request] using
      ExecutableExactDecompositionAlgorithm.children_length_le_budget
        algorithm request

end NearCubicWires.ExecutableInterfaces
