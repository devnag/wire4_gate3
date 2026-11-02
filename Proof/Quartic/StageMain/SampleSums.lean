import Proof.Quartic.StageMain.EntryRequest
import Proof.Quartic.Cells.ParametersOutputBounds

/-!
# Integer prefix sums of the sampled Boolean contributions

Step 4 of `sec:algorithm`, paper/paper.tex,
uses the exact mask and predicate at each chosen sample. Each summand
is zero or one, so a prefix of length `j` increases either total by
at most `j`; casting the complete sum gives the integer totals.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open Algorithm.CellCall
open NearCubicGates.Close.Interfaces

noncomputable def sampleAcceptance (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) : ℕ :=
  if h : j < c.seed.Q then
    (c.pred z (c.samples ⟨j, h⟩) && decide (c.pointMask z (c.samples ⟨j, h⟩) = 1)).toNat
  else 0

noncomputable def sampleMask (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) : ℕ :=
  if h : j < c.seed.Q then (decide (c.pointMask z (c.samples ⟨j, h⟩) = 1)).toNat else 0

noncomputable def sampleAcceptancePrefix (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, sampleAcceptance c z i

noncomputable def sampleMaskPrefix (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, sampleMask c z i

theorem sampleAcceptance_le_one (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) :
    sampleAcceptance c z j ≤ 1 := by
  unfold sampleAcceptance
  split
  · exact Bool.toNat_le _
  · omega

theorem sampleMask_le_one (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) :
    sampleMask c z j ≤ 1 := by
  unfold sampleMask
  split
  · exact Bool.toNat_le _
  · omega

theorem sampleAcceptancePrefix_le (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) :
    sampleAcceptancePrefix c z j ≤ j := by
  calc
    _ ≤ ∑ _i ∈ Finset.range j, (1 : ℕ) :=
      Finset.sum_le_sum (fun _ _ => sampleAcceptance_le_one c z _)
    _ = j := by simp

theorem sampleMaskPrefix_le (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) :
    sampleMaskPrefix c z j ≤ j := by
  calc
    _ ≤ ∑ _i ∈ Finset.range j, (1 : ℕ) :=
      Finset.sum_le_sum (fun _ _ => sampleMask_le_one c z _)
    _ = j := by simp

theorem sampleAcceptancePrefix_succ (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) :
    sampleAcceptancePrefix c z (j + 1) = sampleAcceptancePrefix c z j + sampleAcceptance c z j :=
  Finset.sum_range_succ _ _

theorem sampleMaskPrefix_succ (c : Algorithm.CellCall) (z : Fin c.ncol) (j : ℕ) :
    sampleMaskPrefix c z (j + 1) = sampleMaskPrefix c z j + sampleMask c z j :=
  Finset.sum_range_succ _ _

theorem sampledEntry_acceptance {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q) :
    (entryPredicate (sampledEntryRequest hd w z j) && entryMask (sampledEntryRequest hd w z j)).toNat =
      sampleAcceptance (Program.runCall c p w) z j.val := by
  rw [sampledEntry_predicate, sampledEntry_mask]
  unfold sampleAcceptance
  have hj : j.val < (Program.runCall c p w).seed.Q := j.isLt
  rw [dif_pos hj]
  rfl

theorem sampledEntry_maskNat {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q) :
    (entryMask (sampledEntryRequest hd w z j)).toNat =
      sampleMask (Program.runCall c p w) z j.val := by
  rw [sampledEntry_mask]
  unfold sampleMask
  have hj : j.val < (Program.runCall c p w).seed.Q := j.isLt
  rw [dif_pos hj]
  rfl

end NearQuarticWires.StageMain.Controller
