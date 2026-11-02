import Proof.CaseAnalysis.RawRowsModeDegree
import Proof.CaseAnalysis.RowsUniversalLoad
import Proof.CaseAnalysis.FinalThresholdRows

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open scoped BigOperators
open NearCubicWires
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.RepairSource.CloseoutRowsUniversal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdRowIdentity

noncomputable section

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-! ## 1. The printed row IS the estimator's row (the threshold row polynomial) -/

/-- **The THR printed-form identity at the CORRECTED source.**  Evaluating the printed polynomial
`thresholdRow a r sel …` (the threshold row polynomial's `Q_{g,p,e,f}` at the actual offset `f = f_{g,p}(z)`) on the live and residual coordinate construction's
coded occurrence-residual variables returns the estimator's tuple row
`canonicalOccurrenceCoefficientRadixRow`, i.e.
`CloseoutFinalC10ThresholdRows.selectionRow`.  No `ExecutableExactDecompositionAlgorithm`. -/
theorem thresholdRow_eq_canonical (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable (thresholdFourfoldOccurrences r)
            (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
        (thresholdRow a r sel liveScale denominator prime.val
          (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
            (ThresholdRows.equation a r sel) prime.val) seed) =
      canonicalOccurrenceCoefficientRadixRow
        (digits := modulusDigitCount prime.val)
        (thresholdFourfoldOccurrences r) liveScale denominator input
        Finset.univ
        (modularCoefficientResidue (ThresholdRows.equation a r sel) prime.val)
        seed prime.val
        (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
          (ThresholdRows.equation a r sel) prime.val) := by
  rw [thresholdRow, evaluateStructuralCanonicalOccurrenceCoefficientRadixRow,
    executableCanonicalOccurrenceCoefficientRadixRow_refines]

/-- The same identity written at the estimator's own name for the tuple row. -/
theorem thresholdRow_eq_selectionRow (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable (thresholdFourfoldOccurrences r)
            (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
        (thresholdRow a r sel liveScale denominator prime.val
          (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
            (ThresholdRows.equation a r sel) prime.val) seed) =
      CloseoutFinalC10ThresholdRows.selectionRow a r liveScale denominator input sel prime seed :=
  thresholdRow_eq_canonical a r liveScale denominator input sel prime seed

/-! ## 2. The row degree bound — the per-row preprocessing budget, with NO `|G|` factor -/

/-- At one external label `(g,p,e,f)`, the printed threshold row has at most `rowCountBase ^ modulusDigitCount p` internal radix tuples and raw monomial degree at most `modulusDigitCount p * coordinateDegree`. The exponent is `modulusDigitCount p`, independent of `Fintype.card (ThresholdRows.Selection a r)`. 


-/
theorem thresholdRow_degree_le (sel : ThresholdRows.Selection a r)
    (liveScale denominator : ℕ) {cutoff : ℕ} (prime : PrimeIndex cutoff) (offset : ℕ)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    (thresholdRow a r sel liveScale denominator prime.val offset seed).length ≤
        rowCountBase (thresholdFourfoldOccurrences r) liveScale denominator ^
          modulusDigitCount prime.val ∧
      RawMonomialDegreeAtMost
        (modulusDigitCount prime.val *
          coordinateDegree (thresholdFourfoldOccurrences r) liveScale denominator)
        (thresholdRow a r sel liveScale denominator prime.val offset seed) :=
  ⟨threshold_count a r sel liveScale denominator prime.val offset seed,
    threshold_degree a r sel liveScale denominator prime.val offset seed⟩

/-- The printed threshold row fits the printer's digit width.
This supplies `hmon` for `C10SupplierRowInput.rowInput` in
`Proof/CaseAnalysis/FinalSupplierRowInput.lean` and hence the `w` used
by `raw_cuts_gate` in `Proof/CaseAnalysis/RawRowsLoad.lean`.
The external label `g` is paid in preparation rather than in `s_gen`;
the polynomial exponent remains `modulusDigitCount prime.val`. -/
theorem thresholdRow_printed_fit (sel : ThresholdRows.Selection a r)
    (live : Finset (Fin r.q)) (liveScale denominator ell childBits : ℕ)
    {cutoff : ℕ} (prime : PrimeIndex cutoff) (offset : ℕ)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator)
    (hell : natBitLength (2 * (thresholdFourfoldOccurrences r).length + 1) ≤ ell)
    (hchildren : ∀ i : Fin (pool live (thresholdFourfoldOccurrences r)).length,
      (ExtDecompositionBatch.children a
        ((pool live (thresholdFourfoldOccurrences r)).get i)).length ≤ 2 ^ childBits) :
    (lower a live (thresholdFourfoldOccurrences r)
        (thresholdRow a r sel liveScale denominator prime.val offset seed)).length <
      2 ^ actualWidth (thresholdFourfoldOccurrences r) liveScale denominator
        (modulusDigitCount prime.val) ell (childBits + 1) :=
  row_digit_fit a live (thresholdFourfoldOccurrences r) liveScale denominator
    (modulusDigitCount prime.val) ell childBits _
    (threshold_count a r sel liveScale denominator prime.val offset seed)
    (threshold_degree a r sel liveScale denominator prime.val offset seed) hell hchildren

/-! ## 3. Where the paper's label `g` lives: OUTSIDE the printed row -/

/-- One prime's row VALUE is the aggregation, over the construction's external label `g`, of the
EVALUATIONS of `Fintype.card (ThresholdRows.Selection a r)` separate printed rows.  The threshold row aggregation does the
`g`-sum on the tables `T_{g,p,e,f}(z)`, not inside `Q_{g,p,e,f}`; this is that step. -/
theorem primeRow_eq_printedDisjunction (liveScale denominator : ℕ) (input : BitInput r.q)
    {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    CloseoutFinalC10ThresholdRows.primeRow a r liveScale denominator input prime seed =
      finiteBoolDisjunction (fun sel : ThresholdRows.Selection a r =>
        evaluateStructuralGF2
          (encodedFiniteBooleanAssignment fun index =>
            occurrenceResidualVariable (thresholdFourfoldOccurrences r)
              (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
          (thresholdRow a r sel liveScale denominator prime.val
            (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
              (ThresholdRows.equation a r sel) prime.val) seed)) := by
  unfold CloseoutFinalC10ThresholdRows.primeRow
  exact congrArg finiteBoolDisjunction
    (funext fun sel =>
      (thresholdRow_eq_selectionRow a r liveScale denominator input sel prime seed).symm)

/-- The threshold row at `(p,e)` aggregates the evaluations of separate
printed rows, one for each `g`. The `g`-sum is outside each polynomial
`Q_{g,p,e,f}`; `fourfoldRow_eq_printedDisjunction` gives that identity. -/
theorem fourfoldRow_eq_printedDisjunction (liveScale target : ℕ) (input : BitInput r.q)
    (sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
      NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)) :
    CloseoutFinalC10ThresholdRows.fourfoldRow a r liveScale target input sample =
      finiteBoolDisjunction (fun sel : ThresholdRows.Selection a r =>
        evaluateStructuralGF2
          (encodedFiniteBooleanAssignment fun index =>
            occurrenceResidualVariable (thresholdFourfoldOccurrences r)
              (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
          (thresholdRow a r sel liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r target) sample.1.val
            (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
              (ThresholdRows.equation a r sel) sample.1.val) sample.2)) :=
  primeRow_eq_printedDisjunction a r liveScale
    (CloseoutFinalC10ThresholdRows.listDenominator a r target) input sample.1 sample.2

/-- The external-row count of `thresholdRows` enumerates only the prime
`p` and amplified-list seed `e`. It has no
`Fintype.card (ThresholdRows.Selection a r)` factor.
`fourfoldRow_eq_printedDisjunction` aggregates `g` outside the printed
polynomial, and `thresholdRow_degree_le` gives exponent
`modulusDigitCount prime.val`. The normalization is
`1/(|\mathcal P_q||\mathcal E|2^q)`. 

-/
theorem thresholdRows_rowCount (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (theta : SourceInterfaces.PrimeThetaBoundContract)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    (CloseoutFinalC10ThresholdRows.thresholdRows spectrum theta a liveScale
        targetDenominator).rowCount r =
      Fintype.card
        (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r (targetDenominator r.q)) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q))) := by
  simp only [CloseoutFinalC10ThresholdRows.thresholdRows]

end

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdRowIdentity
