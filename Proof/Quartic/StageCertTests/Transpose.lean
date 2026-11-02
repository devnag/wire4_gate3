import Proof.Quartic.StageRecovery.TableCongruence
import Proof.Quartic.StagePrint.FullTable

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.TabMachine

/-- `imp:pullback` and `lem:print`, paper/paper.tex: swapping separated halves changes only the order
of the two center indices. -/
def transposeCut (c : MatrixScoreBatch.Cut) : MatrixScoreBatch.Cut :=
  {c with leftWeights := c.rightWeights, rightWeights := c.leftWeights}

/-- `lem:print`, paper/paper.tex:
the native request retains all dimensions and the common center map
while interchanging the separated halves of every physical cut. -/
def transposeRequest (r : MatrixScoreBatch.Request) : MatrixScoreBatch.Request where
  d := r.d
  p := r.p
  cuts := r.cuts.map transposeCut
  width := r.width
  column := r.column
  widthLe := r.widthLe
  columnFits := r.columnFits
  lengths := by
    intro c hc
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hc
    exact ⟨(r.lengths original ho).2,(r.lengths original ho).1⟩
  fits := by
    intro c hc
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hc
    obtain ⟨hw,ht,hc⟩ := r.fits original ho
    refine ⟨?_,ht,hc⟩
    intro w hw'
    apply hw
    rcases List.mem_append.mp hw' with hright | hleft
    · exact List.mem_append_right _ hright
    · exact List.mem_append_left _ hleft
  gateSquare := by simpa using r.gateSquare

/-- `lem:print`, paper/paper.tex:
transposition preserves the exact shared center transformation. -/
theorem transposeRequest_phi (r : MatrixScoreBatch.Request) (x : ℕ) :
    (transposeRequest r).phi x = r.phi x := rfl

/-- `lem:print`, paper/paper.tex:
each transposed cut has the original value at reversed indices. -/
theorem transposeCut_value (c : MatrixScoreBatch.Cut) (x y : ℕ) :
    StageRecovery.cutValue (transposeCut c) x y = StageRecovery.cutValue c y x := by
  have hp : (c.threshold - MatrixScoreBatch.linearForm c.rightWeights x ≤
      MatrixScoreBatch.linearForm c.leftWeights y) ↔
    (c.threshold - MatrixScoreBatch.linearForm c.leftWeights y ≤
      MatrixScoreBatch.linearForm c.rightWeights x) := by omega
  have hd : decide (c.threshold - MatrixScoreBatch.linearForm c.rightWeights x ≤
      MatrixScoreBatch.linearForm c.leftWeights y) =
    decide (c.threshold - MatrixScoreBatch.linearForm c.leftWeights y ≤
      MatrixScoreBatch.linearForm c.rightWeights x) := decide_eq_decide.mpr hp
  exact congrArg (fun b : Bool => c.coefficient * (b.toNat : ℤ)) hd

/-- `lem:print`, paper/paper.tex:
the actual dominance table is transposed by changing the raw cuts,
with no subsequent table permutation or repeated table scan. -/
theorem transposeRequest_table (r : MatrixScoreBatch.Request) (i j : Fin r.U) :
    StagePrint.cutTable (transposeRequest r) i j = StagePrint.cutTable r j i := by
  rw [StageRecovery.cutTable_eq_sum,StageRecovery.cutTable_eq_sum]
  change ((r.cuts.map transposeCut).map (fun c =>
    StageRecovery.cutValue c (r.phi i.val) (r.phi j.val))).sum = _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  exact transposeCut_value c _ _

/-- `lem:print`, paper/paper.tex:
the signed native printer can use the transposed cut request
without changing its physical dimension or census hypotheses. -/
def transposeTableRequest (r : StagePrint.TableRequest) : StagePrint.TableRequest where
  matrix := transposeRequest r.matrix
  cuts_le := by simpa [transposeRequest,MatrixScoreBatch.Request.U] using r.cuts_le

/-- `lem:print`, paper/paper.tex:
the transposed native output is row-major in the reversed indices,
so its outer loop is the original center's high half. -/
theorem transposeTableRequest_output (r : StagePrint.TableRequest) :
    (transposeTableRequest r).output =
      NearCubicGates.Close.WordPrograms.recStream
        ((pvals false (fun i j => StagePrint.cutTable r.matrix j i)).map fun z =>
          NearCubicWires.RepairOrdinary.SignedSortKey.binary (r.q+1)
            (NearCubicGates.Close.WordPrograms.SInt.encS z)) := by
  unfold StagePrint.TableRequest.output
  have ht : StagePrint.cutTable (transposeRequest r.matrix) =
      fun i j => StagePrint.cutTable r.matrix j i := by
    funext i j
    exact transposeRequest_table r.matrix i j
  change NearCubicGates.Close.WordPrograms.recStream
    ((pvals false (StagePrint.cutTable (transposeRequest r.matrix))).map _) = _
  rw [ht]
  rfl

end NearQuarticWires.StageCertTests
