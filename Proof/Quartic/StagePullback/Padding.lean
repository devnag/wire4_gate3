import Proof.Quartic.StagePullback.SideCount
import Proof.Quartic.StagePullback.FieldOutput

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- `imp:pullback` and `lem:print`, paper/paper.tex: pad the actual native signed encoding list by literal zero
records to the shared Hamming width. -/
def padNumbers (W : ℕ) (xs : List ℕ) : List ℕ := xs ++ List.replicate (W - xs.length) 0

/-- `imp:pullback`, paper/paper.tex: actual side-count
bounds give the exact common native field count. -/
theorem padNumbers_length (W : ℕ) (xs : List ℕ) (h : xs.length ≤ W) :
    (padNumbers W xs).length = W := by simp [padNumbers]; omega

/-- `imp:pullback`, paper/paper.tex: padding retains
every actual signed field and supplies zero at every added coordinate. -/
theorem padNumbers_getD (W : ℕ) (xs : List ℕ) (i : ℕ) :
    (padNumbers W xs).getD i 0 = xs.getD i 0 := by
  unfold padNumbers
  by_cases h : i < xs.length
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default xs 0 (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

/-- `lem:print`, paper/paper.tex: emitting the
actual native fields and then zero fields equals padded indexed output. -/
theorem range_getD_pad (W : ℕ) (xs : List ℕ) (h : xs.length ≤ W) :
    (List.range W).map (fun i => xs.getD i 0) = padNumbers W xs := by
  apply List.ext_getElem
  · simp [padNumbers_length W xs h]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    rw [← padNumbers_getD W xs i, List.getD_eq_getElem _ _ hj]

/-- `lem:print`, paper/paper.tex: actual indexed
binary record serialization is exactly the padded native record stream. -/
theorem indexed_records_pad (L W : ℕ) (xs : List ℕ) (h : xs.length ≤ W) :
    (List.range W).flatMap (fun i => frame (binary L (xs.getD i 0))) =
      (padNumbers W xs).flatMap (fun v => frame (binary L v)) := by
  have hh := congrArg (fun ys : List ℕ => ys.flatMap (fun v => frame (binary L v)))
    (range_getD_pad W xs h)
  simpa only [List.flatMap_map, Function.comp_def] using hh

end NearQuarticWires.StagePullback.NativeRows
