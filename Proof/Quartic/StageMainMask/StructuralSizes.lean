import Proof.Quartic.StageMainMask.StructuralFormat
import Proof.Quartic.StageMain.FieldExtractSizes
import Proof.Quartic.StageLift.FormulaBytes

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- `imp:partition` and `prop:time`, paper/paper.tex: every actual pattern code has binary length bounded by
the selected dimension field already present in the finite prep word. -/
theorem structural_index_bits {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    natBitLength r.left.val ≤ (Program.prepWord B1 B2 r.call r.witness).length ∧
    natBitLength r.right.val ≤ (Program.prepWord B1 B2 r.call r.witness).length := by
  let hs := Cells.prepare_spec _ r.selected.1 r.selected.2
  have hN : (Program.runCall r.call r.selected r.witness).seed.N = r.selected.1.N := hs.seed_N
  have hnb : natBitLength r.selected.1.N ≤ (Program.parametersWord r.selected.1).length :=
    parameter_bitLength_le_word r.selected.1 _ (by simp [parameterHeadFields, parameterHeadScalars])
  have hp : (Program.parametersWord r.selected.1).length ≤
      (Program.prepWord B1 B2 r.call r.witness).length := by
    rw [prepWord_eq_compact r.dispatched]
    simp only [compactInput, preparedPrefixWord, List.length_append, List.length_cons]
    omega
  have hu : r.left.val ≤ r.selected.1.N := r.left.isLt.le.trans hN.le
  have hv : r.right.val ≤ r.selected.1.N := r.right.isLt.le.trans hN.le
  exact ⟨(codec_nbl_mono hu).trans (hnb.trans hp), (codec_nbl_mono hv).trans (hnb.trans hp)⟩

/-- `prop:time`, paper/paper.tex: the shared
structural input has at most five times the original finite preparation
length plus the two natural-field delimiters. -/
theorem structuralWord_length {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    (structuralWord r).length ≤ 5 * (Program.prepWord B1 B2 r.call r.witness).length + 2 := by
  have hh := structural_index_bits r
  simp only [structuralWord, List.length_append, natWord_length]
  omega

/-- `prop:time`, paper/paper.tex: source parser
workspace depends only on the literal leading arity header. -/
def structuralSizes (B1 B2 : ℕ) : Sz :=
  ⟨10 * (capacityCoefficient B1 + 3), capacityExponent B1 B2, 0, 0, 0, 0⟩

/-- `prop:time`, paper/paper.tex: the exact shared
request keeps the original successful-dispatch arity header. -/
theorem structural_header {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    leadOnes (structuralWord r) = 1 + natBitLength r.call.n := by
  rw [structuralWord, prepWord_eq_compact r.dispatched]
  simp only [compactInput, preparedPrefixWord, List.cons_append, List.append_assoc]
  exact taggedCall_header_width r.call _

/-- `prop:time`, paper/paper.tex: the physical
arity-header workspace covers the complete actual finite request. -/
theorem structuralSizes_width {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    (structuralWord r).length + 2 ≤ (structuralSizes B1 B2).W (leadOnes (structuralWord r)) := by
  have hlen := structuralWord_length r
  have hw := compactInput_width r.dispatched r.witness
  rw [← prepWord_eq_compact r.dispatched] at hw
  rw [structural_header]
  have heq : (structuralSizes B1 B2).W (1 + natBitLength r.call.n) =
      10 * widthAt B1 B2 r.call.n := by
    unfold structuralSizes Sz.W widthAt
    ring
  rw [heq]
  omega

/-- `prop:time`, paper/paper.tex: every structural
workspace includes the fixed arithmetic parser constants. -/
theorem structuralSizes_min (B1 B2 L : ℕ) : 64 ≤ (structuralSizes B1 B2).W L := by
  have h := fieldExtractSizes_min B1 B2 L
  have heq : (structuralSizes B1 B2).W L = 10 * (fieldExtractSizes B1 B2).W L := by
    unfold structuralSizes fieldExtractSizes Sz.W
    ring
  rw [heq]
  omega

end NearQuarticWires.StageMainMask
