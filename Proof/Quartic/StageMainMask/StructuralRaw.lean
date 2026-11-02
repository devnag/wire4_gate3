import Proof.Quartic.StageMainMask.StructuralFields
import Proof.Quartic.StageOutput.PaddingDispatch

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageCert.Incidence

/-- `def:mask`, paper/paper.tex: the internal finite
structural call contains the literal original circuit and the exact
scalar geometry and pattern indices produced from the preparation word. -/
structure StructuralRawRequest where
  call : Call
  partition : StarParams
  arity : partition.n = call.n
  arity_le_call : call.n ≤ (callWord call).length
  threshold : ℕ
  left : Fin ((partition.b + 1) ^ (partition.r / 2))
  right : Fin ((partition.b + 1) ^ (partition.r / 2))

/-- `def:mask`, paper/paper.tex: the original call
precedes the five binary scalar fields; no incidence vector is encoded. -/
def StructuralRawRequest.word (r : StructuralRawRequest) : List Bool :=
  callWord r.call ++ (structuralFields r.partition r.threshold r.left r.right).flatMap
    (fun f => natWord f.2)

/-- `def:mask`, paper/paper.tex: the structural
value uses the original source occurrence degrees and canonical
left and right star-pattern decoders. -/
noncomputable def StructuralRawRequest.bit (r : StructuralRawRequest) : Bool :=
  Mask.structuralMask (r.partition.flipSet r.partition.leftBlock)
    (r.partition.flipSet r.partition.rightBlock)
    (Mask.heavyCoordinates (fun i => sourceDegree r.call i.val) r.threshold)
    ((errorsEquiv r.partition).symm r.left) ((errorsEquiv r.partition).symm r.right)

/-- `prop:time`, paper/paper.tex: the finite actual
source pays for its original arity and all scalar field bit lengths. -/
theorem StructuralRawRequest.encoding_bounds (r : StructuralRawRequest) :
    r.call.n ≤ r.word.length ∧
      ∀ f ∈ structuralFields r.partition r.threshold r.left r.right,
        natBitLength f.2 ≤ r.word.length := by
  constructor
  · exact r.arity_le_call.trans (by simp [StructuralRawRequest.word])
  · intro f hf
    have h := (natBitLength_le_len f.2).trans
      (StageOutput.fieldWord_length _ f hf)
    exact h.trans (by simp [StructuralRawRequest.word])

/-- `imp:partition` and `def:mask`, paper/paper.tex: the literal source covers every block inspected by
the structural mask, and its radix is controlled by the original arity. -/
theorem StructuralRawRequest.geometry_bounds (r : StructuralRawRequest) :
    r.partition.b * r.partition.r ≤ r.call.n ∧
      r.partition.b ≤ r.call.n ∧ r.partition.r ≤ r.call.n := by
  have hb : r.partition.b ≤ r.partition.n :=
    (show r.partition.b ≤ r.partition.r * r.partition.b by
      simpa using Nat.mul_le_mul_right r.partition.b
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt r.partition.r_pos))).trans
      r.partition.r_mul_b_le
  have hr : r.partition.r ≤ r.partition.n := by
    have h := r.partition.four_r_le_n
    omega
  exact ⟨by simpa only [r.arity, Nat.mul_comm] using r.partition.r_mul_b_le,
    by rwa [r.arity] at hb, by rwa [r.arity] at hr⟩

/-- `prop:time`, paper/paper.tex: the actual
call traversal, field parsing and both source-mask scans share one
finite-source arithmetic budget. -/
def structuralRawSteps (r : StructuralRawRequest) (L : ℕ) : ℕ :=
  3000 * (L + 2) ^ 3 +
    StageOutput.readScalarsCost (structuralFields r.partition r.threshold r.left r.right) +
      2 * (r.partition.r / 2) * (1204 * (L + 2) ^ 3 + 2) + 80

end NearQuarticWires.StageMainMask
