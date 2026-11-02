import Proof.Quartic.StageMainMask.PointPacking

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePullback

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: the same actual center and pattern codes
are reused for each of the four independently selected corners. -/
def cornerRequest (q : PointRequest) (left right : Bool) : PointRequest :=
  { q with useLeft := left, useRight := right }

/-- `imp:partition`, paper/paper.tex: a fixed corner
selection is written as an actual zero or one arithmetic variable. -/
def writePointFlag (reg : Fin VV) (bit : Bool) : St VV MM :=
  if bit then .op (.copy reg v1) else .op (.zero reg)

/-- `imp:partition` and `prop:time`, paper/paper.tex: one fixed corner bit is physically written in one step. -/
theorem writePointFlag_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (reg : Fin VV) (hne : reg ≠ v1) (bit : Bool) :
    Hs C (writePointFlag reg bit) a 1 (fun b => b = a.set reg bit.toNat) := by
  cases bit with
  | false => exact hs_zero C reg a
  | true => simpa only [writePointFlag, Bool.toNat_true, if_true, hc.one] using hs_copy C reg v1 a hne

/-- `imp:partition`, paper/paper.tex: two retained
corner flags are set without changing any canonical center metadata. -/
def writeCornerFlags (left right : Bool) : St VV MM :=
  .seq (writePointFlag Flips.leftFlag left) (writePointFlag Flips.rightFlag right)

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: physically changing the two corner selectors
retains the exact original center, translation and sampled errors. -/
theorem PointData.flags {a : DS VV MM} {q : PointRequest} (h : PointData a q)
    (left right : Bool) :
    PointData ((a.set Flips.leftFlag left.toNat).set Flips.rightFlag right.toNat)
      (cornerRequest q left right) := by
  let b := (a.set Flips.leftFlag left.toNat).set Flips.rightFlag right.toNat
  have hf : Fr a b [Flips.leftFlag, Flips.rightFlag] :=
    (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))
  refine ⟨h.constants.of_fr hf (by decide), ?_, ?_, ?_,
    (hf _ (by decide)).trans h.half, (hf _ (by decide)).trans h.blockWidth,
    (hf _ (by decide)).trans h.radix⟩
  · intro i
    exact (hf _ (by fin_cases i <;> decide)).trans (h.fields i)
  · exact (DS.set_env_ne _ _ (by decide : Flips.leftFlag ≠ Flips.rightFlag)).trans
      (DS.set_env_self _ _ _)
  · exact DS.set_env_self _ _ _

/-- `imp:partition` and `prop:time`, paper/paper.tex: both actual corner selectors and their exact metadata
relation are obtained by three source-language operations. -/
theorem writeCornerFlags_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (hi : PointData a q) (left right : Bool) :
    Hs C (writeCornerFlags left right) a 3 (fun b =>
      PointData b (cornerRequest q left right) ∧ b.sh = a.sh ∧
      Fr a b [Flips.leftFlag, Flips.rightFlag]) := by
  unfold writeCornerFlags
  refine Hs.seq (t1 := 1) (t2 := 1) (writePointFlag_run C a hi.constants _ (by decide) left) ?_
  rintro b rfl
  have hc : Cst (a.set Flips.leftFlag left.toNat) :=
    hi.constants.of_fr (T := [Flips.leftFlag]) (Fr.set a _ (by simp)) (by decide)
  refine (writePointFlag_run C _ hc _ (by decide) right).mono le_rfl ?_
  rintro d rfl
  exact ⟨hi.flags left right, rfl, (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageMainMask
