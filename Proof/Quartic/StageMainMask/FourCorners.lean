import Proof.Quartic.StageMainMask.PointCorner

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePullback

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the four canonical affine corners are packed in the population
scanner's original C, CU, CV, CUV register order. -/
def produceFourCorners : St VV MM :=
  .seq (produceCorner 0 false false)
    (.seq (produceCorner 1 true false)
      (.seq (produceCorner 2 false true) (produceCorner 3 true true)))

/-- `imp:partition` and `prop:time`, paper/paper.tex: only the two corner flags, four computed point words
and the actual coordinate-loop variables can be modified. -/
def fourCornersScratch : List (Fin VV) :=
  [Flips.leftFlag, Flips.rightFlag, 114, 115, 116, 117] ++ pointPackingScratch

/-- `imp:partition`, paper/paper.tex: one saved
corner uses a subset of the complete four-corner arithmetic variables. -/
private theorem cornerScratch_subset (i : Fin 4) :
    ∀ x ∈ [Flips.leftFlag, Flips.rightFlag, cornerRegister i] ++ pointPackingScratch,
      x ∈ fourCornersScratch := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simp [fourCornersScratch]
    · simp [fourCornersScratch]
    · fin_cases i <;> decide
  · exact List.mem_append_right _ hx

/-- Step 4 of `sec:algorithm`, `imp:partition`, and `prop:time`,
paper/paper.tex: all four
original packed point values are physically computed from the retained
scalar source with exact corner semantics and a paid coordinate clock. -/
theorem produceFourCorners_run (C : Ctx) (q : PointRequest) (a : DS VV MM)
    (hi : PointData a q) (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C produceFourCorners a (4 * pointCornerCost q + 3) (fun b =>
      b.env 114 = (cornerRequest q false false).packed ∧
      b.env 115 = (cornerRequest q true false).packed ∧
      b.env 116 = (cornerRequest q false true).packed ∧
      b.env 117 = (cornerRequest q true true).packed ∧
      PointData b (cornerRequest q true true) ∧ b.sh = a.sh ∧ Fr a b fourCornersScratch) := by
  unfold produceFourCorners
  refine (Hs.seq (t1 := pointCornerCost q) (t2 := 3 * pointCornerCost q + 2)
    (produceCorner_run C q 0 false false a hi hwidth) ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbv, hbi, hbsh, hbfr⟩
  refine (Hs.seq (t1 := pointCornerCost q) (t2 := 2 * pointCornerCost q + 1)
    (produceCorner_run C (cornerRequest q false false) 1 true false b hbi hwidth) ?_).mono
      (by omega) (fun _ h => h)
  rintro c ⟨hcv, hci, hcsh, hcfr⟩
  refine (Hs.seq (t1 := pointCornerCost q) (t2 := pointCornerCost q)
    (produceCorner_run C (cornerRequest q true false) 2 false true c hci hwidth) ?_).mono
      (by omega) (fun _ h => h)
  rintro d ⟨hdv, hdi, hdsh, hdfr⟩
  refine (produceCorner_run C (cornerRequest q false true) 3 true true d hdi hwidth).mono le_rfl ?_
  rintro e ⟨hev, hei, hesh, hefr⟩
  refine ⟨?_, ?_, ?_, hev, hei, hesh.trans (hdsh.trans (hcsh.trans hbsh)),
    (hbfr.weaken (cornerScratch_subset 0)).trans
      ((hcfr.weaken (cornerScratch_subset 1)).trans
        ((hdfr.weaken (cornerScratch_subset 2)).trans (hefr.weaken (cornerScratch_subset 3))))⟩
  · exact (hefr _ (by decide)).trans ((hdfr _ (by decide)).trans ((hcfr _ (by decide)).trans hbv))
  · exact (hefr _ (by decide)).trans ((hdfr _ (by decide)).trans hcv)
  · exact (hefr _ (by decide)).trans hdv

end NearQuarticWires.StageMainMask
