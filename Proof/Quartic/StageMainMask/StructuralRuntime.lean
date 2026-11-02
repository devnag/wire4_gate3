import Proof.Quartic.StageMainMask.StructuralCold
import Proof.Quartic.StageMainMask.StructuralCost
import Proof.Quartic.StageMain.RuntimeSource
import Proof.Quartic.StageCertTests.ParameterReadCost

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- `prop:time`, paper/paper.tex: the complete
source formatter has a cubic source-language clock in any bound on
its literal finite input length. -/
theorem structuralFormatterSteps_le {B1 B2 : ℕ} (r : StructuralRequest B1 B2)
    (S : ℕ) (hS : 1 ≤ S) (hsource : (structuralWord r).length ≤ S) :
    structuralFormatterSteps r ≤ 110000 * S ^ 3 := by
  let witness := Program.witnessPrefix r.call r.selected.1 r.witness
  let prep := compactInput r.call r.selected.1 witness
  have hprep : prep.length ≤ S := by
    have hh : prep.length ≤ (structuralWord r).length := by
      rw [structuralWord, prepWord_eq_compact r.dispatched]
      simp only [List.length_append]
      dsimp only [prep, witness]
      omega
    exact hh.trans hsource
  have hp : (Program.parametersWord r.selected.1).length ≤ S := by
    have hh := (StageMain.Runtime.compact_lengths r.call r.selected.1 witness).2.1
    exact hh.trans hprep
  have hr : parameterReadCost r.selected.1 prep.length ≤ 20000 * S ^ 2 := by
    calc
      _ ≤ 5000 * ((Program.parametersWord r.selected.1).length + 1) * (prep.length + 1) :=
        StageCertTests.parameterReadCost_le_word _ _
      _ ≤ 5000 * (S + 1) * (S + 1) := by gcongr
      _ ≤ _ := by nlinarith only [hS]
  have hi := StageMain.Runtime.initializeCost_le r.call r.selected.1 witness S hS hprep hr
  change initializeCost r.call r.selected.1 witness prep.length ≤ 100000 * S ^ 3 at hi
  have hb := structural_metadata_bits r
  have hu := (hb r.left.val (by simp)).trans hsource
  have hv := (hb r.right.val (by simp)).trans hsource
  have hread := StageGamma.readFieldsCost_le [r.left.val, r.right.val] S (by
    intro v hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl <;> assumption)
  simp only [List.length_cons, List.length_nil] at hread
  have hcall : (callWord r.call).length ≤ S :=
    (StageMain.Runtime.compact_lengths r.call r.selected.1 witness).1.trans hprep
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have h03 : 1 ≤ S ^ 3 := Nat.pow_pos hS
  change initializeCost r.call r.selected.1 witness prep.length +
    StageGamma.readFieldsCost [r.left.val, r.right.val] + 1 +
    20 * (callWord r.call).length + 400 * (structuralWord r).length + 3001 ≤ _
  omega

/-- `prop:time`, paper/paper.tex: the actual raw
structural request is linear in its original finite prepared source,
including all five binary metadata fields. -/
theorem structuralRawRequest_length {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    (structuralRawRequest r).word.length ≤ 16 * ((structuralWord r).length + 1) := by
  have hb := structural_metadata_bits r
  have h1 := hb r.selected.1.dstar (by simp)
  have h2 := hb r.selected.1.b (by simp)
  have h3 := hb r.selected.1.r (by simp)
  have h4 := hb r.left.val (by simp)
  have h5 := hb r.right.val (by simp)
  have hc : (callWord r.call).length ≤ (structuralWord r).length := by
    rw [structuralWord, prepWord_eq_compact r.dispatched]
    simp only [compactInput, preparedPrefixWord, List.length_append, List.length_cons]
    omega
  rw [structuralRawRequest_word]
  simp only [List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_nil, natWord_length]
  omega

end NearQuarticWires.StageMainMask
