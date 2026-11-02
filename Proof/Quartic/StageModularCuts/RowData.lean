import Proof.Quartic.StageModularCuts.SetupContract

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: the affine part
of a weak cut contains its two dense weight vectors and threshold. -/
def affineFields (p : ℕ) (c : MatrixScoreBatch.Cut) : List (List Bool) :=
  (c.leftWeights ++ c.rightWeights ++ [c.threshold]).map (MatrixScoreBatch.signMagnitude p)

def affineWord (p : ℕ) (c : MatrixScoreBatch.Cut) : List Bool :=
  (affineFields p c).flatMap frame

/-- `lem:print`, paper/paper.tex: the coefficient is
the final field of the actual weak-cut codec. -/
theorem cutWord_split (p : ℕ) (c : MatrixScoreBatch.Cut) :
    MatrixScoreBatch.cutWord p c = affineWord p c ++ frame (MatrixScoreBatch.signMagnitude p c.coefficient) := by
  simp [MatrixScoreBatch.cutWord, MatrixScoreBatch.fields, affineWord, affineFields, List.flatMap_append, List.flatMap_map]

/-- `lem:print`, paper/paper.tex: a coefficient
reduction preserves every affine-field byte. -/
theorem reducedWord_split (p q : ℕ) (c : MatrixScoreBatch.Cut) :
    MatrixScoreBatch.cutWord p (StageRecovery.reduceCut q c) =
      affineWord p c ++ frame (MatrixScoreBatch.signMagnitude p (c.coefficient % (q : ℤ))) := by
  rw [cutWord_split]
  rfl

/-- `lem:print`, paper/paper.tex: the exact affine
field count includes the threshold even for zero dense width. -/
theorem affineFields_length (p : ℕ) (c : MatrixScoreBatch.Cut) :
    (affineFields p c).length = c.leftWeights.length + c.rightWeights.length + 1 := by
  simp [affineFields, Nat.add_assoc]

/-- `lem:print`, paper/paper.tex: affine field bytes
have one common signed magnitude width. -/
theorem affineWord_length (p : ℕ) (c : MatrixScoreBatch.Cut) :
    (affineWord p c).length = (c.leftWeights.length + c.rightWeights.length + 1) * (2 * p + 3) := by
  unfold affineWord affineFields
  simp only [List.flatMap_map, List.length_flatMap, frame_length,
    MatrixScoreBatch.signMagnitude_length, List.map_const', List.sum_replicate,
    List.length_append, List.length_cons, List.length_nil]
  ring

/-- `lem:print`, paper/paper.tex: reducing a
coefficient retains the entire row's literal byte length. -/
theorem cutWord_length (p : ℕ) (c : MatrixScoreBatch.Cut) :
    (MatrixScoreBatch.cutWord p c).length =
      (c.leftWeights.length + c.rightWeights.length + 2) * (2 * p + 3) := by
  rw [cutWord_split, List.length_append, affineWord_length, frame_length,
    MatrixScoreBatch.signMagnitude_length]
  ring

/-- `lem:print`, paper/paper.tex: a nonempty cut
begins with a frame marker, including when both dense vectors are empty. -/
theorem cutWord_head (p : ℕ) (c : MatrixScoreBatch.Cut) (suffix : List Bool) :
    (MatrixScoreBatch.cutWord p c ++ suffix).headD false = true := by
  cases hl : c.leftWeights <;> cases hr : c.rightWeights <;>
    simp [MatrixScoreBatch.cutWord, MatrixScoreBatch.fields, hl, hr,
      MatrixScoreBatch.signMagnitude, frame]

end NearQuarticWires.StageModularCuts
