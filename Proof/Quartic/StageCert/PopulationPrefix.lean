import Proof.Quartic.StageCert.SelectedGate

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `def:mask`, paper/paper.tex: the exact magnitude of
one original occurrence at the four packed original cell points. -/
def gateMagnitude {n : ℕ} (g : NormalizedThresholdGate n) (points : Fin 4→ℕ) : ℕ :=
  (fourBitDifference (fun l=>g.eval (packedPoint n (points l)))).natAbs

/-- `def:mask`, paper/paper.tex: a prefix of the original
occurrence list contributes only where its literal W2 bit is set. -/
def populationPrefix {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (points : Fin 4→ℕ) (bits : List Bool) (index count : ℕ) : ℕ :=
  ((List.range count).map fun j=>if hj : j<gs.length then
    if Algorithm.witnessBit bits (index+j) then gateMagnitude gs[j] points else 0
    else 0).sum

/-- `def:mask`, paper/paper.tex: adding one actual
occurrence extends the selected population by exactly its signed magnitude. -/
theorem populationPrefix_succ {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (points : Fin 4→ℕ) (bits : List Bool) (index count : ℕ) :
    populationPrefix gs points bits index (count+1)=populationPrefix gs points bits index count+
      (if hj : count<gs.length then
        if Algorithm.witnessBit bits (index+count) then gateMagnitude gs[count] points else 0
      else 0) := by
  simp [populationPrefix,List.range_succ,List.map_append,List.sum_append]

/-- `sec:cells`, paper/paper.tex: even before any cell or
column certificate, each occurrence contributes at most two. -/
theorem gateMagnitude_le_two {n : ℕ} (g : NormalizedThresholdGate n) (points : Fin 4→ℕ) :
    gateMagnitude g points≤2 := fourBitDifference_natAbs_le_two _

/-- `def:mask`, paper/paper.tex: all intermediate
selected-population accumulators have an unconditional source-count bound. -/
theorem populationPrefix_le {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (points : Fin 4→ℕ) (bits : List Bool) (index count : ℕ) :
    populationPrefix gs points bits index count≤2*count := by
  induction count with
  | zero => simp [populationPrefix]
  | succ j ih =>
    rw [populationPrefix_succ]
    by_cases hj : j<gs.length
    · rw [dif_pos hj]
      split
      · have h := gateMagnitude_le_two gs[j] points
        omega
      · omega
    · rw [dif_neg hj]
      omega

end NearQuarticWires.StageCert
