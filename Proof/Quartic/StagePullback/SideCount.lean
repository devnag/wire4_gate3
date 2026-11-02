import Proof.Quartic.StagePullback.RowPrefix

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def sideBit (q : PointRequest) (i : ℕ) : Bool :=
  if hi : i < q.parameters.n then q.parameters.centerSide ⟨i, hi⟩ else false

/-- `imp:partition`, paper/paper.tex: a physical
coordinate prefix has the canonical count of its left-side markers. -/
theorem filter_range_count (p : ℕ → Bool) : ∀ n,
    ((List.range n).filter p).length = PrimT.C4Geo.cnt p n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, filter_range_count p n]
    cases h : p n <;> simp [PrimT.C4Geo.cnt, h]

/-- `imp:partition`, paper/paper.tex: each original
coordinate belongs to exactly one of the two canonical halves. -/
theorem count_complement_add (p : ℕ → Bool) : ∀ n,
    PrimT.C4Geo.cnt p n + PrimT.C4Geo.cnt (fun i => !(p i)) n = n
  | 0 => rfl
  | n + 1 => by
    have h := count_complement_add p n
    cases hp : p n <;> simp only [PrimT.C4Geo.cnt, hp, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] <;> omega

/-- `imp:partition`, paper/paper.tex: the canonical
left coordinates have exactly the shared Hamming half width. -/
theorem side_count_width (q : PointRequest) :
    PrimT.C4Geo.cnt (sideBit q) q.parameters.n = PrimT.C4Geo.width q.parameters := by
  have h := PrimT.C4Geo.cnt_side q.parameters q.parameters.n
  change PrimT.C4Geo.cnt (sideBit q) q.parameters.n = _ at h
  rw [h]
  have hhalf : q.parameters.r / 2 * q.parameters.b ≤ q.parameters.n :=
    (Nat.mul_le_mul_right _ (Nat.div_le_self q.parameters.r 2)).trans q.parameters.r_mul_b_le
  have hfree := PrimT.C4Geo.hL_le q.parameters
  unfold PrimT.C4Geo.cntL PrimT.C4Geo.width
  rw [Nat.min_eq_right hhalf, Nat.min_eq_right hfree, Nat.add_sub_cancel_left]

/-- `imp:pullback`, paper/paper.tex: physical
transposition only exchanges the two exact canonical side counts. -/
theorem rowNumbers_length (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose isLeft : Bool) :
    (rowNumbers q e transpose isLeft q.parameters.n).length =
      if xor transpose isLeft then PrimT.C4Geo.width q.parameters
      else q.parameters.n - PrimT.C4Geo.width q.parameters := by
  have hfilter : (List.range q.parameters.n).filter
      (fun i => coordinateSide q transpose i == isLeft) =
      (List.range q.parameters.n).filter
        (if xor transpose isLeft then sideBit q else fun i => !(sideBit q i)) := by
    apply List.filter_congr
    intro i hi
    have hi' := List.mem_range.mp hi
    cases transpose <;> cases isLeft <;> simp [coordinateSide, sideBit, hi']
  simp only [rowNumbers, List.length_map]
  rw [hfilter]
  cases h : xor transpose isLeft
  · simp only [Bool.false_eq_true, if_false]
    rw [filter_range_count]
    have hc := count_complement_add (sideBit q) q.parameters.n
    rw [side_count_width] at hc
    omega
  · simp only [if_true]
    rw [filter_range_count, side_count_width]

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: both actual native halves fit the same canonical
Hamming width, including odd free-coordinate counts and transposition. -/
theorem rowNumbers_length_le (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose isLeft : Bool) :
    (rowNumbers q e transpose isLeft q.parameters.n).length ≤ PrimT.C4Geo.width q.parameters := by
  have hrb := PrimT.C4Geo.rb_eq q.parameters
  have hblk := q.parameters.r_mul_b_le
  have hbalance : q.parameters.n - PrimT.C4Geo.width q.parameters ≤ PrimT.C4Geo.width q.parameters := by
    unfold PrimT.C4Geo.width PrimT.C4Geo.hL
    omega
  rw [rowNumbers_length]
  split <;> first | exact le_rfl | exact hbalance

end NearQuarticWires.StagePullback.NativeRows
