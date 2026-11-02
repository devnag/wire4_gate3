import Proof.Quartic.StageLift.MemoryVariable
import Proof.Quartic.Greedy.Child

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells

/-- `cor:conditional` and Step 3, paper/paper.tex: the decoded coefficient's original sign and magnitude. -/
def gammaSignVar : Fin VV := ⟨124, by decide⟩
def gammaMagnitudeVar : Fin VV := ⟨125, by decide⟩

/-- Step 3, `sec:algorithm`, paper/paper.tex: the actual requested
positive or negative part and the resulting nonnegative coefficient. -/
def partVar : Fin VV := ⟨126, by decide⟩
def splitCoefficientVar : Fin VV := ⟨127, by decide⟩

/-- Step 3, `sec:algorithm`, paper/paper.tex: extract exactly the
nonnegative magnitude of the requested signed coefficient part. -/
def splitMagnitude (side : Bool) (z : ℤ) : ℕ :=
  if decide (z < 0) = side then 0 else z.natAbs

/-- Step 3, `sec:algorithm`, paper/paper.tex: the byte-level sign
selection is the literal positive/negative split used by Greedy. -/
theorem splitMagnitude_eq (side : Bool) (z : ℤ) :
    (splitMagnitude side z : ℤ) = if side then max z 0 else max (-z) 0 := by
  cases side with
  | false =>
      by_cases hz : z < 0
      · simp [splitMagnitude, hz, abs_of_neg hz,
          max_eq_left (by omega : 0 ≤ -z)]
      · simp [splitMagnitude, hz, max_eq_right (by omega : -z ≤ 0)]
  | true =>
      by_cases hz : z < 0
      · simp [splitMagnitude, hz, max_eq_right hz.le]
      · simp [splitMagnitude, hz, abs_of_nonneg (le_of_not_gt hz),
          max_eq_left (le_of_not_gt hz)]

/-- Step 3, `sec:algorithm`, paper/paper.tex: a computed sign bit
selects a stored magnitude without reading a supplied split-weight word. -/
def selectSplitCoefficient : St VV MM :=
  .ite (.eq gammaSignVar partVar) (.op (.zero splitCoefficientVar))
    (.op (.copy splitCoefficientVar gammaMagnitudeVar))

/-- Step 3, `sec:algorithm`, paper/paper.tex: the actual binary
selection computes Greedy's coefficient part and preserves all source
and output streams and every unrelated runtime field. -/
theorem selectSplitCoefficient_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (side : Bool) (z : ℤ)
    (hsign : a.env gammaSignVar = (decide (z < 0)).toNat)
    (hmag : a.env gammaMagnitudeVar = z.natAbs) (hpart : a.env partVar = side.toNat) :
    Hs C selectSplitCoefficient a 2 (fun b =>
      b.env splitCoefficientVar = splitMagnitude side z ∧ b.sh = a.sh ∧
      Cst b ∧ Fr a b [splitCoefficientVar]) := by
  unfold selectSplitCoefficient
  by_cases heq : decide (z < 0) = side
  · have ht : (Cnd.eq gammaSignVar partVar).eval a = true := by
      simp [Cnd.eval, hsign, hpart, heq]
    refine (Hs.iteT (c := .eq gammaSignVar partVar) (show gammaSignVar ≠ partVar by decide)
      ht (hs_zero C splitCoefficientVar a)).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [splitMagnitude, heq], rfl,
      Cst.of_fr (T := [splitCoefficientVar]) hc (Fr.set a _ (by simp)) (by decide),
      Fr.set a _ (by simp)⟩
  · have ht : (Cnd.eq gammaSignVar partVar).eval a = false := by
      have hne : (decide (z < 0)).toNat ≠ side.toNat := by
        cases hn : decide (z < 0) <;> cases hs : side <;> simp_all
      simpa only [Cnd.eval, hsign, hpart, decide_eq_false_iff_not] using hne
    refine (Hs.iteF (c := .eq gammaSignVar partVar) (show gammaSignVar ≠ partVar by decide)
      ht (hs_copy C splitCoefficientVar gammaMagnitudeVar a (by decide))).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [splitMagnitude, heq, hmag], rfl,
      Cst.of_fr (T := [splitCoefficientVar]) hc (Fr.set a _ (by simp)) (by decide),
      Fr.set a _ (by simp)⟩

end NearQuarticWires.StageLift
