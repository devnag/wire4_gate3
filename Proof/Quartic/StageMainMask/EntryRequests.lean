import Proof.Quartic.StageMainMask.EntryPoints
import Proof.Quartic.StageMainMask.StructuralRequest
import Proof.Quartic.StageMainMask.PopulationRequest
import Proof.Quartic.StageCert.PopulationBuilder
import Proof.Quartic.Program.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Interfaces
open StageMain StagePullback

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual field sample supplies the two original indices of the shared
structural-mask request, retaining the literal preparation source. -/
noncomputable def entryStructuralRequest {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    StructuralRequest B1 B2 :=
  ⟨r.call, r.selected, r.dispatched, r.witness, (entryPosition r).1, (entryPosition r).2⟩

/-- `def:mask`, paper/paper.tex: the structural
reply belongs to the actual sampled original column. -/
theorem entryStructuralRequest_bit {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    structuralBit (entryStructuralRequest r) =
      ((entryCall r).column r.column).structural (entryPosition r) := rfl

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the selected population is evaluated at the original center, left error,
right error and both errors, in that exact source order. -/
noncomputable def entryCorners {B1 B2 : ℕ} (r : EntryRequest B1 B2) : Fin 4 → ℕ :=
  ![(entryPointRequest r false false).packed, (entryPointRequest r true false).packed,
    (entryPointRequest r false true).packed, (entryPointRequest r true true).packed]

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: decoding the physically packed original
point recovers every one of its original Boolean coordinates. -/
theorem packedPoint_pointRequest (q : PointRequest) :
    packedPoint q.parameters.n q.packed = q.point := by
  funext i
  change (CanonicalBinary.bitsValue (List.ofFn q.point)).testBit i.val = _
  rw [PrimT.C4Geo.testBit_bitsValue, List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn, Fin.eta]

/-- Witness (W2) and `def:mask`, paper/paper.tex: the retained finite witness contains every selected
original occurrence bit, including both complete raw gate banks. -/
theorem entrySelection_fits {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    r.selected.1.k + r.call.first.gates.length + r.call.second.gates.length ≤
      (Program.witnessPrefix r.call r.selected.1 r.witness).length := by
  simp only [Program.witnessPrefix, List.length_ofFn, Program.witnessReadLength]
  have h : r.call.first.gates.length + r.call.second.gates.length ≤
      (r.selected.1.J + 1) * (r.call.first.gates.length + r.call.second.gates.length) :=
    Nat.le_mul_of_pos_left _ (by omega)
  change r.selected.1.k + r.call.first.gates.length + r.call.second.gates.length ≤
    r.selected.1.k + (r.selected.1.J + 1) *
      (r.call.first.gates.length + r.call.second.gates.length)
  omega

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the population request contains the actual original call, physically
computed four points and the actual finite retained selection source. -/
noncomputable def entryPopulationRequest {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    PopulationRequest where
  call := r.call
  arity_le_call := Cells.dispatched_n_le_callWord r.dispatched
  offset := r.selected.1.k
  corners := entryCorners r
  witness := Program.witnessPrefix r.call r.selected.1 r.witness
  selection_fits := entrySelection_fits r

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: the population source reply is exactly
the original sampled column's integer population, without dropping
occurrences, changing selection bits or replacing magnitude two by one. -/
theorem entryPopulationRequest_value {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryPopulationRequest r).value = ((entryCall r).column r.column).X (entryPosition r) := by
  let hs := Cells.prepare_spec _ r.selected.1 r.selected.2
  have hx := StageCert.builder_X_eq_populationPrefix r.call hs r.witness r.column
    (entryPosition r).1 (entryPosition r).2 (entryCorners r)
    (by
      change packedPoint r.call.n (entryPointRequest r false false).packed = _
      exact (packedPoint_pointRequest (entryPointRequest r false false)).trans
        (entryPointRequest_center r))
    (by
      change packedPoint r.call.n (entryPointRequest r true false).packed = _
      apply (packedPoint_pointRequest (entryPointRequest r true false)).trans
      funext i
      simp only [entryPointRequest, PointRequest.point, Bool.true_and, Bool.false_and,
        Bool.xor_false, Shared.xorInput]
      rfl)
    (by
      change packedPoint r.call.n (entryPointRequest r false true).packed = _
      apply (packedPoint_pointRequest (entryPointRequest r false true)).trans
      funext i
      simp only [entryPointRequest, PointRequest.point, Bool.true_and, Bool.false_and,
        Bool.xor_false, Shared.xorInput]
      rfl)
    (by
      change packedPoint r.call.n (entryPointRequest r true true).packed = _
      exact (packedPoint_pointRequest (entryPointRequest r true true)).trans
        (entryPointRequest_both r))
  unfold PopulationRequest.value entryPopulationRequest
  rw [← List.length_append]
  change StageCert.populationPrefix (Builder.allGates r.call) (entryCorners r)
    (Program.witnessPrefix r.call r.selected.1 r.witness) r.selected.1.k
    (Builder.allGates r.call).length = _
  change _ = (Builder.columnData r.call hs r.witness r.column).X (entryPosition r)
  trans StageCert.populationPrefix (Builder.allGates r.call) (entryCorners r)
    r.witness r.selected.1.k (Builder.allGates r.call).length
  swap
  · exact hx.symm
  rw [StageCert.populationPrefix_eq_sum, StageCert.populationPrefix_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Program.witnessBit_witnessPrefix]
  have hi : i.val < r.call.first.gates.length + r.call.second.gates.length := by
    simpa only [Builder.allGates, List.length_append] using i.isLt
  have h := entrySelection_fits r
  simp only [Program.witnessPrefix, List.length_ofFn] at h
  omega

end NearQuarticWires.StageMainMask
