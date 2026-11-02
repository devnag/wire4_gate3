import Proof.Quartic.StagePullback.PointBit
import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePullback

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: a partial point accumulator contains the
literal low-coordinate prefix of the actual canonical affine point. -/
def pointPrefix (q : PointRequest) (k : ℕ) : ℕ :=
  CanonicalBinary.bitsValue ((List.ofFn q.point).take k)

/-- `imp:partition`, paper/paper.tex: the empty
coordinate prefix has its exact zero encoding. -/
theorem pointPrefix_zero (q : PointRequest) : pointPrefix q 0 = 0 := rfl

/-- `imp:partition`, paper/paper.tex: every partial
canonical point occupies at most its actual number of source bits. -/
theorem pointPrefix_lt (q : PointRequest) (k : ℕ) : pointPrefix q k < 2 ^ k := by
  have hh := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.bitsValue_lt
    ((List.ofFn q.point).take k)
  exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by simp))

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: appending the actual computed coordinate
bit gives the exact next low-first packed point prefix. -/
theorem pointPrefix_succ (q : PointRequest) (k : ℕ) (hk : k < q.parameters.n) :
    pointPrefix q (k + 1) = pointPrefix q k + (q.point ⟨k, hk⟩).toNat * 2 ^ k := by
  unfold pointPrefix
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.bitsValue_take_succ _ _
    (by simpa using hk)]
  congr 2
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp only [List.getElem_ofFn]

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: processing all original coordinates gives
the actual point word consumed by the original circuit evaluator. -/
theorem pointPrefix_full (q : PointRequest) : pointPrefix q q.parameters.n = q.packed := by
  unfold pointPrefix PointRequest.packed
  exact congrArg CanonicalBinary.bitsValue (by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn q.point)))

end NearQuarticWires.StageMainMask
