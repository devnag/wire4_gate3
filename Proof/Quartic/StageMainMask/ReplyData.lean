import Proof.Quartic.StageMainMask.CallData
import Proof.Quartic.StageMainMask.PopulationReply

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageMain StageMain.Compact StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the structural answer, original predicate answer and final mask occupy
fixed variables disjoint from all retained original source fields. -/
def structuralFlag : Fin VV := 44
def predicateValue : Fin VV := 45
def numericMaskValue : Fin VV := 46

/-- `prop:time`, paper/paper.tex: every actual
source writer, reply parser and population comparison uses only this
fixed finite set of native scalar variables. -/
def entryEvaluationScratch : List (Fin VV) := sourceWriterScratch ++
  populationReplyScratch ++ [structuralFlag, predicateValue, numericMaskValue]

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual reply decoders can change their separate retained reply
store while preserving the three original finite source records and
every physically computed original point and selection parameter. -/
theorem EntryNumericData.of_evaluation {B1 B2 : ℕ} {r : EntryRequest B1 B2}
    {a b : DS VV MM} (h : EntryNumericData r a)
    (hprep : b.ram compactStore = a.ram compactStore)
    (hcall : b.ram callStore = a.ram callStore)
    (hwit : b.ram witnessStore = a.ram witnessStore)
    (hf : Fr a b entryEvaluationScratch) : EntryNumericData r b := by
  refine ⟨hprep.trans h.prepared, hcall.trans h.originalCall, hwit.trans h.witness,
    (hf _ (by decide)).trans h.preparedLength, (hf _ (by decide)).trans h.callLength,
    (hf _ (by decide)).trans h.witnessLength, (hf _ (by decide)).trans h.left,
    (hf _ (by decide)).trans h.right, ?_,
    (hf _ (by decide)).trans h.cutoff, (hf _ (by decide)).trans h.offset⟩
  intro i
  exact (hf _ (by fin_cases i <;> decide)).trans (h.corners i)

end NearQuarticWires.StageMainMask
