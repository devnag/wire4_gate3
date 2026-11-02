import Proof.Quartic.StageCertTests.WholeSchedule
import Proof.Quartic.StageCertTests.OrdinalPlan

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicGates.Close.Interfaces

/-- `eq:testE`, paper/paper.tex:
the physical chain length is exactly the number of digit tests
in the selected mathematical walk data. -/
theorem digitMetadataList_eq_ordinals (p : Cells.Parameters) (hJ : 1 ≤ p.J)
    (j : Fin 2) (code : Fin 256) :
    digitMetadataList p j code =
      (List.ofFn fun r : Fin ((p.J-1)+1) => (TestOrdinal.digit j code r).metadata p) := by
  apply List.ext_getElem
  · simp only [digitMetadataList,List.length_ofFn]
    omega
  · intro i hi hi'
    simp only [digitMetadataList,List.getElem_ofFn,digitMetadata,TestOrdinal.metadata]
    congr 1
    simp [ThresholdKind.threshold,ThresholdKind.field,ThresholdKind.increment,
      ThresholdKind.multiplier,ScheduleField.value,Nat.mul_comm]

/-- `eq:testE`–`eq:testPhi`, paper/paper.tex:
each physically printed sign block has precisely the digit and
final-error metadata of the literal ordinal test plan. -/
theorem patternMetadataList_eq_ordinals (p : Cells.Parameters) (hJ : 1 ≤ p.J)
    (j : Fin 2) (code : Fin 256) :
    patternMetadataList p j code =
      ((List.ofFn fun r : Fin ((p.J-1)+1) => TestOrdinal.digit j code r) ++
        [TestOrdinal.finalError j code]).map (TestOrdinal.metadata p) := by
  rw [List.map_append,List.map_ofFn,List.map_cons,List.map_nil]
  unfold patternMetadataList
  rw [digitMetadataList_eq_ordinals p hJ]
  congr 1
  simp [TestOrdinal.metadata,ThresholdKind.threshold,ThresholdKind.field,ThresholdKind.increment,
    ThresholdKind.multiplier,ScheduleField.value,Nat.mul_comm]

/-- `sec:cycle` and `sec:algorithm`, paper/paper.tex: the physical sign filter preserves the
complete literal order of all required whole-test requests. -/
theorem circuitMetadataList_eq_ordinals (p : Cells.Parameters) (hJ : 1 ≤ p.J) (j : Fin 2) :
    circuitMetadataList p j = (List.finRange 256).flatMap (fun code =>
      if Cycle.kappa 4 (patternOfCode code.val) ≠ 0 then
        ((List.ofFn fun r : Fin ((p.J-1)+1) => TestOrdinal.digit j code r) ++
          [TestOrdinal.finalError j code]).map (TestOrdinal.metadata p) else []) := by
  simp only [circuitMetadataList,circuitMetadataBlocks,List.ofFn_eq_map,List.flatten_eq_flatMap,
    List.flatMap_map,id_eq]
  apply congrArg (fun f : Fin 256 → List TestMetadata => (List.finRange 256).flatMap f)
  funext code
  by_cases hk : Cycle.kappa 4 (patternOfCode code.val) ≠ 0
  · rw [activePatternMetadata,if_pos hk,if_pos hk]
    simpa only [List.ofFn_eq_map,List.map_append,List.map_cons,List.map_nil,List.map_map] using
      patternMetadataList_eq_ordinals p hJ j code
  · simp [activePatternMetadata,hk]

/-- `sec:algorithm`, paper/paper.tex:
the literal call-kind circuit set has the exact order generated
by the physical one- or two-circuit loop. -/
theorem circuitMetadataForLimit_eq_circuitSet (c : Call) (p : Cells.Parameters) :
    circuitMetadataForLimit p (callCircuitCount c.kind) (callCircuitCount_bounds c.kind).2 =
      (List.finRange 2).flatMap (fun j =>
        if j ∈ Builder.circuitSet c then circuitMetadataList p j else []) := by
  cases hk : c.kind <;>
    simp [circuitMetadataForLimit,callCircuitCount,hk,Builder.circuitSet,List.finRange]

/-- `sec:algorithm`, paper/paper.tex:
the complete physical metadata stream names exactly the literal
whole-test ordinal plan, with no extra or missing sign or digit tests. -/
theorem certificateMetadata_eq_ordinalTestPlan (c : Call) (p : Cells.Parameters) (hJ : 1 ≤ p.J) :
    certificateMetadata p c.kind =
      (ordinalTestPlan (p.J-1) (Builder.circuitSet c)).map (TestOrdinal.metadata p) := by
  rw [certificateMetadata,circuitMetadataForLimit_eq_circuitSet]
  simp only [ordinalTestPlan,List.map_cons,List.map_flatMap,TestOrdinal.metadata]
  congr 1
  · simp [ThresholdKind.threshold,ThresholdKind.field,ThresholdKind.increment,
      ThresholdKind.multiplier,ScheduleField.value,Nat.mul_comm]
  · apply congrArg (fun f : Fin 2 → List TestMetadata => (List.finRange 2).flatMap f)
    funext j
    by_cases hj : j ∈ Builder.circuitSet c
    · simp only [hj,↓reduceIte,List.map_flatMap]
      rw [circuitMetadataList_eq_ordinals p hJ j]
      apply congrArg (fun f : Fin 256 → List TestMetadata => (List.finRange 256).flatMap f)
      funext code
      split_ifs <;> simp
    · simp [hj]

end NearQuarticWires.StageCertTests
