import Proof.Quartic.StageMain.SampleSums

/-!
# The certified-column sums are the literal output totals

Step 4 of `sec:algorithm`, paper/paper.tex,
skips uncertified columns and adds both exact sampled sums for every
certified column. The natural counters below cast to the integer
`acceptTotal` and `maskTotal` used by Step 5.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open Algorithm.CellCall
open Classical

noncomputable def certifiedAcceptance (c : Algorithm.CellCall) (z : Fin c.ncol) : ℕ :=
  if z ∈ c.certifiedColumns then sampleAcceptancePrefix c z c.seed.Q else 0

noncomputable def certifiedMask (c : Algorithm.CellCall) (z : Fin c.ncol) : ℕ :=
  if z ∈ c.certifiedColumns then sampleMaskPrefix c z c.seed.Q else 0

noncomputable def columnAcceptance (c : Algorithm.CellCall) (i : ℕ) : ℕ :=
  if h : i < c.ncol then certifiedAcceptance c ⟨i, h⟩ else 0

noncomputable def columnMask (c : Algorithm.CellCall) (i : ℕ) : ℕ :=
  if h : i < c.ncol then certifiedMask c ⟨i, h⟩ else 0

noncomputable def columnAcceptancePrefix (c : Algorithm.CellCall) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, columnAcceptance c j

noncomputable def columnMaskPrefix (c : Algorithm.CellCall) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, columnMask c j

theorem certifiedAcceptance_le (c : Algorithm.CellCall) (z : Fin c.ncol) :
    certifiedAcceptance c z ≤ c.seed.Q := by
  unfold certifiedAcceptance
  split
  · exact sampleAcceptancePrefix_le _ _ _
  · omega

theorem certifiedMask_le (c : Algorithm.CellCall) (z : Fin c.ncol) :
    certifiedMask c z ≤ c.seed.Q := by
  unfold certifiedMask
  split
  · exact sampleMaskPrefix_le _ _ _
  · omega

theorem columnAcceptancePrefix_le (c : Algorithm.CellCall) (i : ℕ) :
    columnAcceptancePrefix c i ≤ i * c.seed.Q := by
  calc
    _ ≤ ∑ _j ∈ Finset.range i, c.seed.Q := by
      apply Finset.sum_le_sum
      intro j _
      unfold columnAcceptance
      split
      · exact certifiedAcceptance_le _ _
      · omega
    _ = _ := by simp

theorem columnMaskPrefix_le (c : Algorithm.CellCall) (i : ℕ) :
    columnMaskPrefix c i ≤ i * c.seed.Q := by
  calc
    _ ≤ ∑ _j ∈ Finset.range i, c.seed.Q := by
      apply Finset.sum_le_sum
      intro j _
      unfold columnMask
      split
      · exact certifiedMask_le _ _
      · omega
    _ = _ := by simp

theorem columnAcceptancePrefix_succ (c : Algorithm.CellCall) (z : Fin c.ncol) :
    columnAcceptancePrefix c (z.val + 1) =
      columnAcceptancePrefix c z.val + certifiedAcceptance c z := by
  rw [columnAcceptancePrefix, Finset.sum_range_succ]
  unfold columnAcceptance
  rw [dif_pos z.isLt]
  rfl

theorem columnMaskPrefix_succ (c : Algorithm.CellCall) (z : Fin c.ncol) :
    columnMaskPrefix c (z.val + 1) = columnMaskPrefix c z.val + certifiedMask c z := by
  rw [columnMaskPrefix, Finset.sum_range_succ]
  unfold columnMask
  rw [dif_pos z.isLt]
  rfl

theorem sampleAcceptancePrefix_cast (c : Algorithm.CellCall) (z : Fin c.ncol) :
    (sampleAcceptancePrefix c z c.seed.Q : ℤ) =
      ∑ j : Fin c.seed.Q, bitInt (c.pred z (c.samples j)) * c.pointMask z (c.samples j) := by
  unfold sampleAcceptancePrefix
  rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  unfold sampleAcceptance
  rw [dif_pos j.isLt]
  have hm := Program.CellBounds.pointMask_mem c z (c.samples j)
  have hm' : c.pointMask z (c.samples j) = 0 ∨ c.pointMask z (c.samples j) = 1 := by omega
  rcases hm' with hm' | hm' <;> cases c.pred z (c.samples j) <;> simp [hm', bitInt]

theorem sampleMaskPrefix_cast (c : Algorithm.CellCall) (z : Fin c.ncol) :
    (sampleMaskPrefix c z c.seed.Q : ℤ) = ∑ j : Fin c.seed.Q, c.pointMask z (c.samples j) := by
  unfold sampleMaskPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  unfold sampleMask
  rw [dif_pos j.isLt]
  have hm := Program.CellBounds.pointMask_mem c z (c.samples j)
  have hm' : c.pointMask z (c.samples j) = 0 ∨ c.pointMask z (c.samples j) = 1 := by omega
  rcases hm' with hm' | hm' <;> simp [hm']

theorem columnAcceptancePrefix_cast (c : Algorithm.CellCall) :
    (columnAcceptancePrefix c c.ncol : ℤ) = Program.acceptTotal c := by
  unfold columnAcceptancePrefix
  rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  calc
    _ = ∑ z : Fin c.ncol, if z ∈ c.certifiedColumns then
        ∑ j : Fin c.seed.Q, bitInt (c.pred z (c.samples j)) * c.pointMask z (c.samples j) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      unfold columnAcceptance
      rw [dif_pos z.isLt]
      simp only [certifiedAcceptance]
      split
      · exact sampleAcceptancePrefix_cast _ _
      · rfl
    _ = Program.acceptTotal c := by simp [Program.acceptTotal]

theorem columnMaskPrefix_cast (c : Algorithm.CellCall) :
    (columnMaskPrefix c c.ncol : ℤ) = Program.maskTotal c := by
  unfold columnMaskPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  calc
    _ = ∑ z : Fin c.ncol, if z ∈ c.certifiedColumns then
        ∑ j : Fin c.seed.Q, c.pointMask z (c.samples j) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      unfold columnMask
      rw [dif_pos z.isLt]
      simp only [certifiedMask]
      split
      · exact sampleMaskPrefix_cast _ _
      · rfl
    _ = Program.maskTotal c := by simp [Program.maskTotal]

end NearQuarticWires.StageMain.Controller
