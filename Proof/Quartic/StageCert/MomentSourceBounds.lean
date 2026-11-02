import Proof.Quartic.StageCert.MomentSourceCopy
import Proof.Quartic.StageCert.MomentFlagSource

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- `lem:print`, paper/paper.tex: the actual
preparation record is a literal prefix of every original moment source. -/
theorem MomentRequest.prep_length_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (Program.prepWord B1 B2 r.call r.witness).length≤r.word.length := by
  rw [r.word_source_layout,List.length_append]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: every parsed numeric source field has bit length
bounded by its actual finite input, without a decoded-height premise. -/
theorem MomentRequest.value_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (value : ℕ) (hv : value∈r.sourceValues) : natBitLength value≤r.word.length := by
  obtain ⟨l,t,heq⟩ := List.mem_iff_append.mp hv
  have hword : (natWord value).length≤(r.sourceValues.flatMap natWord).length := by
    rw [heq]
    simp only [List.flatMap_append,List.flatMap_cons,List.length_append]
    omega
  have hnat := NearCubicGates.Close.Dispatch.natBitLength_le_len value
  rw [r.word_source_layout,List.length_append]
  omega

/-- `sec:params` and `lem:print`, paper/paper.tex: the selected walk radix is physically present in the
original preparation word and therefore has no uncharged bit height. -/
theorem MomentRequest.base_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    natBitLength r.selected.1.N≤r.word.length := by
  have hnb : natBitLength r.selected.1.N≤(Program.parametersWord r.selected.1).length :=
    parameter_bitLength_le_word r.selected.1 _ (by simp [parameterHeadFields,parameterHeadScalars])
  have hp : (Program.parametersWord r.selected.1).length≤
      (Program.prepWord B1 B2 r.call r.witness).length := by
    rw [prepWord_eq_compact r.dispatched]
    simp only [compactInput,preparedPrefixWord,List.length_append,List.length_cons]
    omega
  exact hnb.trans (hp.trans r.prep_length_le)

/-- `sec:walks`, `lem:print` and `prop:time`, paper/paper.tex: the literal cold input
width alone pays the radix division and all actual callee-input fields. -/
theorem MomentRequest.source_widths {B1 B2 : ℕ} (r : MomentRequest B1 B2) (width : ℕ)
    (hwidth : r.word.length+2≤width) :
    2≤width ∧ (Program.prepWord B1 B2 r.call r.witness).length<2^width ∧
      2*r.selected.1.N≤2^width ∧
      (∀edge,natBitLength (r.edgeRequest edge).left.val+2<2^width) ∧
      (∀edge,natBitLength (r.edgeRequest edge).right.val+2<2^width) := by
  have hwp : width<2^width := Nat.lt_two_pow_self
  have hn : r.selected.1.N<2^natBitLength r.selected.1.N := lt_natBitLength _
  have hnp : 2^(natBitLength r.selected.1.N+1)≤2^width :=
    Nat.pow_le_pow_right (by decide) (by have hh := r.base_bits; omega)
  rw [pow_succ] at hnp
  refine ⟨by omega,by have hh := r.prep_length_le; omega,by omega,?_,?_⟩
  · intro edge
    have hh := (StageMainMask.structural_index_bits (r.edgeRequest edge)).1
    change natBitLength (r.edgeRequest edge).left.val≤
      (Program.prepWord B1 B2 r.call r.witness).length at hh
    have hp := r.prep_length_le
    omega
  · intro edge
    have hh := (StageMainMask.structural_index_bits (r.edgeRequest edge)).2
    change natBitLength (r.edgeRequest edge).right.val≤
      (Program.prepWord B1 B2 r.call r.witness).length at hh
    have hp := r.prep_length_le
    omega

end NearQuarticWires.StageCert.Tokens
