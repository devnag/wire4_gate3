import Proof.CaseAnalysis.FinalRealizes
import Proof.CaseAnalysis.FinalLengthGate

namespace NearCubicWires.RepairSource.CloseoutFinal.C10Verdict

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness
open RepairRepresentation CompetitorRationalGap ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open CloseoutRowsOriginalSchedule
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The admissible range for each phase's validity and acceptance tests. -/
def bound {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    Phase → ℝ
  | .penalty => 2*((zeta constants : ℚ) : ℝ)
  | .moment => 1+((zeta constants : ℚ) : ℝ)
  | .clause => ((midpoint constants : ℚ) : ℝ)

/-- The three-phase verdict, fused with the length gate over ONE execution. -/
structure Verdict {t s : ℕ} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (pcpp : PointwisePCPP circuit)
    (proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (evaluate : Atom → BitInput n → Bool)
    (p : Machine t s) (ht : 2 ≤ t) (budget : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (result : Fin t) (ports : Phase → Fin t) (width : Phase → ℕ) where
  /-- Paper: reject every length below the soundness cutoff. -/
  gate : LengthGate constants p ht result budget
  heads : Fin t → ℕ
  exit : Fin t → List Bool
  /-- **The machine halts at EVERY length.** Above the cutoff this is the
  estimator's run; below it, the gate's rejection (`gated_reject`). `StepAtInputs`
  needs both, so the run is unconditional while the three `Realizes` are not. -/
  run : Step p (budget len) (fun _ => 0)
    ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) heads exit
  /-- One `Realizes` per phase, at the SAME run, above the cutoff. -/
  realizes : Soundness.cutoff constants ≤ len → ∀ ph : Phase,
    Realizes ph constants pcpp proofValue evaluate p (budget len) (fun _ => 0)
      ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits)
      (ports ph) (width ph)
  /-- Determinism of `runFrom` makes this true; it is a field so the sharing is
  syntactic rather than re-derived at every use. -/
  hshared : ∀ (h : Soundness.cutoff constants ≤ len) (ph : Phase),
    (realizes h ph).exit = exit
  /-- The three estimated reals of the weak machine construction. -/
  estimate : Phase → ℝ
  hestimate : ∀ (h : Soundness.cutoff constants ≤ len) (ph : Phase),
    estimate ph = (((realizes h ph).result.value : ℚ) : ℝ)
  /-- The weak machine construction validity and the componentwise phase calculation acceptance, exactly. -/
  accepts_iff : readTapeBit (exit result) (heads result) = true ↔
    (Soundness.cutoff constants ≤ len ∧
      estimate .penalty ≤ bound constants .penalty ∧
      estimate .moment ≤ bound constants .moment ∧
      bound constants .clause ≤ estimate .clause)

variable {t s : ℕ} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
variable {source : PointwisePCPPAlgorithm} {constants : Constants source}
variable {pcpp : PointwisePCPP circuit}
variable {proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
variable {evaluate : Atom → BitInput n → Bool}
variable {p : Machine t s} {ht : 2 ≤ t} {budget : ℕ → ℕ}
variable {len : ℕ} {x : BitInput len} {bits : List Bool}
variable {result : Fin t} {ports : Phase → Fin t} {width : Phase → ℕ}

/-- **Accuracy at the verdict.** Every estimated real the verdict compares is
within `eps_est` of the exact mean for its phase. -/
theorem accurate_of_verdict
    (V : Verdict constants pcpp proofValue evaluate p ht budget len x bits result ports width)
    (h : Soundness.cutoff constants ≤ len) (ph : Phase) :
    |V.estimate ph - CloseoutRowsOriginalSchedule.mean ph pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  rw [V.hestimate h ph]
  exact accurate_of_realizes (V.realizes h ph)

/-- Acceptance is only possible above the cutoff. This is the conjunct `Exposes`
demands, read straight off the verdict. -/
theorem cutoff_of_accepts
    (V : Verdict constants pcpp proofValue evaluate p ht budget len x bits result ports width)
    (hacc : readTapeBit (V.exit result) (V.heads result) = true) :
    Soundness.cutoff constants ≤ len :=
  (V.accepts_iff.mp hacc).1

/-- **Soundness direction of the componentwise phase calculation.** Acceptance yields the three threshold facts
together with the cutoff. -/
theorem thresholds_of_accepts
    (V : Verdict constants pcpp proofValue evaluate p ht budget len x bits result ports width)
    (hacc : readTapeBit (V.exit result) (V.heads result) = true) :
    Soundness.cutoff constants ≤ len ∧
      V.estimate .penalty ≤ bound constants .penalty ∧
      V.estimate .moment ≤ bound constants .moment ∧
      bound constants .clause ≤ V.estimate .clause :=
  V.accepts_iff.mp hacc

/-- **Completeness direction of the componentwise phase calculation.** The three threshold facts above the
cutoff force acceptance. This is what `SymDecides` consumes. -/
theorem accepts_of_thresholds
    (V : Verdict constants pcpp proofValue evaluate p ht budget len x bits result ports width)
    (h : Soundness.cutoff constants ≤ len)
    (hp : V.estimate .penalty ≤ bound constants .penalty)
    (hm : V.estimate .moment ≤ bound constants .moment)
    (hc : bound constants .clause ≤ V.estimate .clause) :
    readTapeBit (V.exit result) (V.heads result) = true :=
  V.accepts_iff.mpr ⟨h, hp, hm, hc⟩

/-- The unconditional halting fact, in the shape `StepAtInputs` consumes. -/
theorem step_of_verdict
    (V : Verdict constants pcpp proofValue evaluate p ht budget len x bits result ports width) :
    ∃ hout tout, Step p (budget len) (fun _ => 0)
      ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) hout tout :=
  ⟨V.heads, V.exit, V.run⟩

end
end NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
