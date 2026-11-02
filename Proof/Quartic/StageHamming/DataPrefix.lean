import Proof.Quartic.StageHamming.Parity
import Mathlib.Data.List.GetD

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition`, paper/paper.tex: the data
positions encountered before the current coordinate of a block scan. -/
def dataPrefix (s k : ℕ) : List ℕ :=
  (List.range k).filter fun i => !parityPrefix i s

/-- `imp:partition`, paper/paper.tex: appending one
candidate position changes the list precisely when it is not a parity
position of the canonical Hamming code. -/
theorem dataPrefix_succ (s k : ℕ) :
    dataPrefix s (k + 1) =
      if parityPrefix k s then dataPrefix s k else dataPrefix s k ++ [k] := by
  cases hp : parityPrefix k s <;>
    simp [dataPrefix, List.range_succ, hp]

/-- `imp:partition`, paper/paper.tex: a data-position
scan has counted at most the number of coordinates it has visited. -/
theorem dataPrefix_length_le (s k : ℕ) : (dataPrefix s k).length ≤ k := by
  simpa [dataPrefix] using List.length_filter_le (fun i => !parityPrefix i s) (List.range k)

/-- `imp:partition`, paper/paper.tex: a retained
default-zero position changes exactly when a newly appended list entry
has the requested index, including every out-of-range request. -/
theorem getD_append_singleton_zero (l : List ℕ) (x m : ℕ) :
    (l ++ [x]).getD m 0 = if m = l.length then x else l.getD m 0 := by
  by_cases hlt : m < l.length
  · rw [List.getD_append _ _ _ _ hlt, if_neg (Nat.ne_of_lt hlt)]
  · have hle : l.length ≤ m := by omega
    rw [List.getD_append_right _ _ _ _ hle]
    by_cases heq : m = l.length
    · subst m; simp
    · have hpos : 1 ≤ m - l.length := by omega
      rw [if_neg heq, List.getD_eq_default _ _ hpos,
        List.getD_eq_default _ _ hle]

/-- `imp:partition`, paper/paper.tex: the canonical
position lookup satisfies the exact update implemented by the scalar
scan, with no precomputed basis table. -/
theorem dataPrefix_getD_succ (s k m : ℕ) :
    (dataPrefix s (k + 1)).getD m 0 =
      if parityPrefix k s then (dataPrefix s k).getD m 0
      else if m = (dataPrefix s k).length then k else (dataPrefix s k).getD m 0 := by
  rw [dataPrefix_succ]
  cases parityPrefix k s with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact getD_append_singleton_zero _ _ _
  | true => simp only [if_true]

/-- `imp:partition`, paper/paper.tex: a completed
coordinate scan is the literal increasing list used to define the
canonical Hamming code, rather than a substituted basis. -/
theorem dataPrefix_eq_dataPos (P : StarParams) :
    dataPrefix P.s P.b = PrimT.C4Geo.dataPos P := rfl

/-- `imp:partition`, paper/paper.tex: the scalar scan's
default-zero lookup agrees with the literal canonical data position. -/
theorem dataPrefix_getD_eq_dpos (P : StarParams) (m : ℕ) :
    (dataPrefix P.s P.b).getD m 0 = PrimT.C4Geo.dpos P m := rfl

end NearQuarticWires.StageHamming
