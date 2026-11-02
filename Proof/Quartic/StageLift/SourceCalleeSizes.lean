import Proof.Quartic.StageLift.MasksContract
import Proof.Quartic.StageLift.SourceWidth
import Proof.Quartic.StageMainMask.StructuralScale

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the proved
actual structural source has one fixed ordinary-machine coefficient. -/
noncomputable def sourceStructuralBudgetFactor : ℕ :=
  Classical.choose StageMainMask.structuralBudget_scale + 1

/-- `prop:time`, paper/paper.tex: the actual
structural source clock is bounded before any callee reserve is chosen. -/
theorem source_structural_budget_factor {B1 B2 : ℕ} (r : StageMainMask.StructuralRequest B1 B2) :
    StageMainMask.structuralBudget r ≤
      sourceStructuralBudgetFactor * (StageMainMask.structuralScale B1 B2 r.call.n) ^ 12 := by
  exact (Classical.choose_spec StageMainMask.structuralBudget_scale B1 B2 r).trans
    (Nat.mul_le_mul_right _ (by unfold sourceStructuralBudgetFactor; omega))

/-- `prop:time`, paper/paper.tex: one fixed
coefficient bounds the actual structural header allocation and machine
dimensions, independently of witness, walk and raw index suffix. -/
noncomputable def sourceStructuralScaleCoefficient (B1 B2 : ℕ) : ℕ :=
  10 * (StageMain.Compact.capacityCoefficient B1 + 3) +
    StageMain.Compact.capacityExponent B1 B2 + TSK StageGamma.fieldProducerCallee + VV + MM + 1002

/-- `prop:time`, paper/paper.tex: the complete
structural source scale is controlled by the original arity header. -/
theorem source_structural_scale_header (B1 B2 n : ℕ) :
    StageMainMask.structuralScale B1 B2 n ≤
      sourceStructuralScaleCoefficient B1 B2 *
        2 ^ (StageMain.Compact.capacityExponent B1 B2 * (1 + natBitLength n)) := by
  have hd : 0 < StageMain.Compact.capacityExponent B1 B2 := by
    unfold StageMain.Compact.capacityExponent
    exact Nat.mul_pos (by omega) (by omega)
  have hExp : natBitLength n ≤ StageMain.Compact.capacityExponent B1 B2 *
      (1 + natBitLength n) := by
    exact (show natBitLength n ≤ 1 + natBitLength n by omega).trans
      (Nat.le_mul_of_pos_left _ hd)
  have hn : n ≤ 2 ^ (StageMain.Compact.capacityExponent B1 B2 * (1 + natBitLength n)) :=
    (lt_natBitLength n).le.trans (Nat.pow_le_pow_right (by decide) hExp)
  have hp : 1 ≤ 2 ^ (StageMain.Compact.capacityExponent B1 B2 * (1 + natBitLength n)) :=
    Nat.pow_pos (by decide)
  have hfixed := Nat.mul_le_mul_left
    (StageMain.Compact.capacityExponent B1 B2 + TSK StageGamma.fieldProducerCallee + VV + MM + 1000) hp
  unfold StageMainMask.structuralScale StageMainMask.structuralSizes Sz.W sourceStructuralScaleCoefficient
  nlinarith only [hn, hp, hfixed]

/-- Step 3 and `prop:time`, paper/paper.tex: arithmetic width and real structural-callee input/work
reserves all come from the original small tagged arity header. -/
noncomputable def printSourceSizes (B1 B2 : ℕ) : Sz :=
  ⟨100 * (sourceWidthCoefficient B1 + 1) ^ 2, 2 * sourceWidthExponent B1 B2,
    10 * (StageMain.Compact.capacityCoefficient B1 + 3), StageMain.Compact.capacityExponent B1 B2,
    sourceStructuralBudgetFactor * (sourceStructuralScaleCoefficient B1 B2) ^ 12 + 10,
    12 * StageMain.Compact.capacityExponent B1 B2⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: source arithmetic fits the actual original header,
independently of all following retained-source and raw target lengths. -/
theorem printSourceSizes_width {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (suffix : List Bool) :
    100 * (sourceEnvelope r + 1) ^ 2 ≤
      (printSourceSizes B1 B2).W (leadOnes (Greedy.printInput r ++ suffix)) :=
  source_arithmetic_width r suffix

/-- `def:mask` and `prop:time`, paper/paper.tex: every actual structural request fits the real callee
input reserve computed from that same original arity header. -/
theorem source_structural_room {B1 B2 : ℕ} (r : StageMainMask.StructuralRequest B1 B2) :
    (StageMainMask.structuralWord r).length ≤
      (printSourceSizes B1 B2).Lk (1 + natBitLength r.call.n) := by
  have h := StageMainMask.structuralSizes_width r
  rw [StageMainMask.structural_header] at h
  exact (Nat.le_add_right _ 2).trans h

/-- `def:mask` and `prop:time`, paper/paper.tex: the actual proved StructuralCold clock fits its header
reserve, rather than being assumed as a callee-budget premise. -/
theorem source_structural_work {B1 B2 : ℕ} (r : StageMainMask.StructuralRequest B1 B2) :
    StageMainMask.structuralBudget r ≤
      (printSourceSizes B1 B2).Bk (1 + natBitLength r.call.n) := by
  have hb := source_structural_budget_factor r
  have hs := source_structural_scale_header B1 B2 r.call.n
  calc
    _ ≤ sourceStructuralBudgetFactor * (StageMainMask.structuralScale B1 B2 r.call.n) ^ 12 := hb
    _ ≤ sourceStructuralBudgetFactor * (sourceStructuralScaleCoefficient B1 B2 *
        2 ^ (StageMain.Compact.capacityExponent B1 B2 * (1 + natBitLength r.call.n))) ^ 12 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)
    _ = 2 ^ ((12 * StageMain.Compact.capacityExponent B1 B2) * (1 + natBitLength r.call.n)) *
        (sourceStructuralBudgetFactor * (sourceStructuralScaleCoefficient B1 B2) ^ 12) := by
      rw [mul_pow, ← pow_mul,
        show (StageMain.Compact.capacityExponent B1 B2 * (1 + natBitLength r.call.n)) * 12 =
          (12 * StageMain.Compact.capacityExponent B1 B2) * (1 + natBitLength r.call.n) by ring]
      exact (Nat.mul_assoc _ _ _).symm.trans (Nat.mul_comm _ _)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right _ 10)

/-- `lem:print` and `prop:time`, paper/paper.tex: every literal Print edge source receives both actual
input and work reserves from the original source context. -/
theorem printMask_callee_reserves {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) (suffix : List Bool) (edge : Fin 8) :
    (StageMainMask.structuralWord (printMaskStructuralRequest r index edge)).length ≤
        (printSourceSizes B1 B2).Lk (leadOnes (Greedy.printInput r ++ suffix)) ∧
    StageMainMask.structuralBudget (printMaskStructuralRequest r index edge) ≤
        (printSourceSizes B1 B2).Bk (leadOnes (Greedy.printInput r ++ suffix)) := by
  rw [printInput_header_width]
  exact ⟨source_structural_room _, source_structural_work _⟩

end NearQuarticWires.StageLift
