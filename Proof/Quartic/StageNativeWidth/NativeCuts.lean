import Proof.Quartic.StageNativeWidth.RadixStack
import Proof.Quartic.StagePrint.NativeEquations

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Tabulator

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the real typed same-generator equality cuts fit the
actual stack width, using the actual StackRequest radix-power guard. -/
theorem nativeEqualityCuts_fits (r : StageTuple.TermCutRequest) :
    ∀ c ∈ StagePrint.nativeEqualityCuts r, EquationRow.Fits r.stackWidth c := by
  intro c hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨es, hes, rfl⟩ := List.mem_map.mp hc
  let rows := es.map eqF
  have hp : (t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids =
      ((t.1.sort (· ≤ ·)).map (StagePrint.nativeKidsEquations r.toRowContext)).map (List.map eqF) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact (StagePrint.nativeKidsEquations_fields r.toRowContext i).symm
  have hrows : rows ∈ tuples ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids) := by
    rw [hp, tuples_map]
    exact List.mem_map_of_mem hes
  have hlen : rows.length = t.1.card := by
    simpa only [List.length_map, Finset.length_sort] using mem_tuples_length _ rows hrows
  have hst : (magL rows+1)^(rows.length+1) < 2^r.stackWidth := by
    rw [hlen]
    exact r.stack_fit t ht rows hrows
  have hfields : ∀ z ∈ MatrixScoreBatch.fields
      (RowBinLift.split t.2 (SupplierEstimator.canonicalEquationStack es)), z.natAbs < 2^r.stackWidth := by
    intro z hz
    rw [fields_cut] at hz
    exact cutL_abs_of_stack_fit r.stackWidth _ rows t.2 hst (r.coefficient_fit t ht) z hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    apply hfields z
    exact List.mem_append_left _ hz
  · exact hfields _ (by simp [MatrixScoreBatch.fields])
  · exact hfields _ (by simp [MatrixScoreBatch.fields])

/-- `lem:print`, paper/paper.tex: both actual
weak cuts fit at exactly one additional magnitude bit, including the
successor target and the negated signed coefficient. -/
theorem nativeEqualityCuts_weak_fits (r : StageTuple.TermCutRequest)
    (c : MatrixScoreBatch.Cut) (hc : c ∈ StagePrint.nativeEqualityCuts r) :
    EquationRow.Fits (r.stackWidth+1) c ∧
      EquationRow.Fits (r.stackWidth+1) (EquationRow.successor c) :=
  ⟨EquationRow.fits_widen _ _ (nativeEqualityCuts_fits r c hc),
    EquationRow.successor_fits _ _ (nativeEqualityCuts_fits r c hc)⟩

end NearQuarticWires.StageNativeWidth
