import Proof.Quartic.StagePullback.RowCoordinate

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires
open NearCubicGates.Close.WordPrograms

/-- `imp:pullback`, paper/paper.tex: original signed
weights in their physical source-coordinate order. -/
def originalWeight (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (i : ℕ) : ℤ :=
  if hi : i < q.parameters.n then e.weight ⟨i, hi⟩ else 0

def coordinateFlip (q : PointRequest) (i : ℕ) : Bool :=
  if hi : i < q.parameters.n then q.flip ⟨i, hi⟩ else false

def coordinateSide (q : PointRequest) (transpose : Bool) (i : ℕ) : Bool :=
  if hi : i < q.parameters.n then xor (q.parameters.centerSide ⟨i, hi⟩) transpose else false

/-- `imp:pullback`, paper/paper.tex: signed native
records retained after the first k original source coordinates. -/
def rowNumbers (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose isLeft : Bool) (k : ℕ) : List ℕ :=
  ((List.range k).filter fun i => coordinateSide q transpose i == isLeft).map fun i =>
    SInt.encS (if coordinateFlip q i then -originalWeight q e i else originalWeight q e i)

def targetPrefix (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (k : ℕ) : ℤ :=
  ((List.range k).map fun i => if coordinateFlip q i then originalWeight q e i else 0).sum

def massPrefix (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (k : ℕ) : ℕ :=
  ((List.range k).map fun i => if coordinateFlip q i then (originalWeight q e i).natAbs else 0).sum

/-- `imp:pullback`, paper/paper.tex: one actual
coordinate appends its signed record exactly to the computed native side. -/
theorem rowNumbers_succ (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose isLeft : Bool) (k : ℕ) :
    rowNumbers q e transpose isLeft (k + 1) = rowNumbers q e transpose isLeft k ++
      if coordinateSide q transpose k == isLeft then
        [SInt.encS (if coordinateFlip q k then -originalWeight q e k else originalWeight q e k)]
      else [] := by
  by_cases h : coordinateSide q transpose k = isLeft <;>
    simp [rowNumbers, List.range_succ, h]

/-- `imp:pullback`, paper/paper.tex: the exact affine
target prefix gains precisely the original flipped weight. -/
theorem targetPrefix_succ (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (k : ℕ) :
    targetPrefix q e (k + 1) = targetPrefix q e k +
      if coordinateFlip q k then originalWeight q e k else 0 := by
  simp [targetPrefix, List.range_succ]

/-- `prop:time`, paper/paper.tex: the actual
accumulator mass prefix gains exactly the flipped coefficient magnitude. -/
theorem massPrefix_succ (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (k : ℕ) :
    massPrefix q e (k + 1) = massPrefix q e k +
      if coordinateFlip q k then (originalWeight q e k).natAbs else 0 := by
  simp [massPrefix, List.range_succ]

/-- `prop:time`, paper/paper.tex: original fixed
signed field bounds control every physical affine accumulator prefix. -/
theorem massPrefix_le (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (Lin k : ℕ)
    (hk : k ≤ q.parameters.n) (hfit : ∀ i, SInt.encS (e.weight i) < 2 ^ Lin) :
    massPrefix q e k ≤ k * 2 ^ Lin := by
  have hh : ∀ z ∈ ((List.range k).map fun i =>
      if coordinateFlip q i then (originalWeight q e i).natAbs else 0), z ≤ 2 ^ Lin := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    have hi' : i < q.parameters.n := (List.mem_range.mp hi).trans_le hk
    rw [originalWeight, dif_pos hi']
    split_ifs
    · have hf := hfit ⟨i, hi'⟩
      unfold SInt.encS at hf
      split_ifs at hf <;> omega
    · exact Nat.zero_le _
  have hsum : ∀ l : List ℕ, (∀ v ∈ l, v ≤ 2 ^ Lin) → l.sum ≤ l.length * 2 ^ Lin := by
    intro l
    induction l with
    | nil => simp
    | cons v l ih =>
      intro hb
      have hv := hb v (by simp)
      have ht := ih (fun w hw => hb w (by simp [hw]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith
  have hh := hsum _ hh
  simpa only [massPrefix, List.length_map, List.length_range] using hh

end NearQuarticWires.StagePullback.NativeRows
