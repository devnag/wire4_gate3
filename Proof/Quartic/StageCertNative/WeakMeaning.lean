import Proof.Quartic.StageCertNative.WeakPool

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary

private theorem concatenate_weak_stream {n : ℕ} (cuts : Fin n→List MatrixScoreBatch.Cut) (p : ℕ) :
    (List.ofFn (fun i=>(EquationRow.doubled false (cuts i)).flatMap
      (MatrixScoreBatch.cutWord p))).flatten=
      (EquationRow.doubled false (List.ofFn cuts).flatten).flatMap (MatrixScoreBatch.cutWord p) := by
  induction n with
  | zero=>simp [EquationRow.doubled]
  | succ n ih=>
    rw [List.ofFn_succ,List.ofFn_succ,List.flatten_cons,List.flatten_cons]
    simp only [EquationRow.doubled,List.flatMap_append]
    exact congrArg (fun tail=>
      (List.flatMap (MatrixScoreBatch.cutWord p) (EquationRow.doubled false (cuts 0)))++tail)
      (ih (fun i=>cuts i.succ))

/-- `lem:print`, paper/paper.tex: converting
each original term to two weak cuts and concatenating once gives
exactly the signed matrix stream of the single whole-test request. -/
theorem wholeWeakWord_eq_nativeStream {B1 B2 : ℕ} (r : StageCertificateControl.IndexedRequest B1 B2) :
    wholeWeakWord r=(actualTable r).matrix.cuts.flatMap
      (MatrixScoreBatch.cutWord (actualTable r).matrix.p) := by
  change wholeWeakWord r=(EquationRow.doubled false (wholeCuts r)).flatMap
    (MatrixScoreBatch.cutWord (commonWidth r+1))
  have hterm (i : Fin (termCount r)) : termWeakWord ⟨r,i⟩=
      (EquationRow.doubled false (StagePrint.nativeEqualityCuts (termRequest r i))).flatMap
        (MatrixScoreBatch.cutWord (commonWidth r+1)) := by
    change (EquationRow.doubled false (StagePrint.nativeEqualityCuts (termRequest r i))).flatMap
      (MatrixScoreBatch.cutWord ((termRequest r i).stackWidth+1))=_
    rw [termRequest_width r i]
  unfold wholeWeakWord
  simp_rw [hterm]
  exact concatenate_weak_stream (fun i=>StagePrint.nativeEqualityCuts (termRequest r i))
    (commonWidth r+1)

end NearQuarticWires.StageCertNative
