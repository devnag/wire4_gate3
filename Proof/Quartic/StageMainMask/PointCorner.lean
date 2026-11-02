import Proof.Quartic.StageMainMask.PointFlags

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePullback

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the four actually computed original points occupy the exact packed
corner registers used by the population scanner. -/
def cornerRegister (i : Fin 4) : Fin VV := ⟨114 + i.val, by change 114 + i.val < 128; omega⟩

/-- `imp:partition` and `prop:time`, paper/paper.tex: storing a computed point preserves all canonical point
metadata, with no source-coordinate or decoder register overwritten. -/
theorem PointData.saveCorner {a : DS VV MM} {q : PointRequest} (h : PointData a q)
    (i : Fin 4) (v : ℕ) : PointData (a.set (cornerRegister i) v) q := by
  have hf : Fr a (a.set (cornerRegister i) v) [cornerRegister i] := Fr.set a _ (by simp)
  exact ⟨h.constants.of_fr hf (by fin_cases i <;> decide),
    fun j => (hf _ (by fin_cases i <;> fin_cases j <;> decide)).trans (h.fields j),
    (hf _ (by fin_cases i <;> decide)).trans h.useLeft,
    (hf _ (by fin_cases i <;> decide)).trans h.useRight,
    (hf _ (by fin_cases i <;> decide)).trans h.half,
    (hf _ (by fin_cases i <;> decide)).trans h.blockWidth,
    (hf _ (by fin_cases i <;> decide)).trans h.radix⟩

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
one chosen corner is produced by its real coordinate loop and stored,
without assuming a supplied packed-point value. -/
def produceCorner (i : Fin 4) (left right : Bool) : St VV MM :=
  .seq (writeCornerFlags left right)
    (.seq packActualPoint (.op (.copy (cornerRegister i) packedPointRegister)))

/-- `prop:time`, paper/paper.tex: one complete
corner includes both selector writes, the exact point encoder loop
and the final packed-register copy. -/
def pointCornerCost (q : PointRequest) : ℕ :=
  q.parameters.n * (500 * (q.parameters.n + 1) ^ 3 + 9) + 14

/-- Step 4 of `sec:algorithm`, `imp:partition` and `prop:time`,
paper/paper.tex: one actual
corner is computed and saved with exact semantics, preserving the
source and every other corner register. -/
theorem produceCorner_run (C : Ctx) (q : PointRequest) (i : Fin 4) (left right : Bool)
    (a : DS VV MM) (hi : PointData a q) (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C (produceCorner i left right) a (pointCornerCost q) (fun b =>
      b.env (cornerRegister i) = (cornerRequest q left right).packed ∧
      PointData b (cornerRequest q left right) ∧ b.sh = a.sh ∧
      Fr a b ([Flips.leftFlag, Flips.rightFlag, cornerRegister i] ++ pointPackingScratch)) := by
  unfold produceCorner
  refine (Hs.seq (t1 := 3)
    (t2 := q.parameters.n * (500 * (q.parameters.n + 1) ^ 3 + 9) + 10)
    (writeCornerFlags_run C a q hi left right) ?_).mono
      (by unfold pointCornerCost; omega) (fun _ h => h)
  rintro b ⟨hbi, hbsh, hbfr⟩
  refine (Hs.seq (t1 := q.parameters.n * (500 * (q.parameters.n + 1) ^ 3 + 9) + 8)
    (t2 := 1) (packActualPoint_run C (cornerRequest q left right) b hbi hwidth) ?_).mono
      (by omega) (fun _ h => h)
  rintro d ⟨hdpacked, hdi, hdsh, hdfr⟩
  refine (hs_copy C (cornerRegister i) packedPointRegister d
    (by fin_cases i <;> decide)).mono le_rfl ?_
  rintro e rfl
  have hfb : Fr a b ([Flips.leftFlag, Flips.rightFlag, cornerRegister i] ++ pointPackingScratch) :=
    hbfr.weaken (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl <;> simp)
  have hfd : Fr b d ([Flips.leftFlag, Flips.rightFlag, cornerRegister i] ++ pointPackingScratch) :=
    hdfr.weaken (fun _ hx => List.mem_append_right _ hx)
  exact ⟨(DS.set_env_self _ _ _).trans hdpacked, hdi.saveCorner i _, hdsh.trans hbsh,
    hfb.trans (hfd.trans (Fr.set d _ (by simp)))⟩

end NearQuarticWires.StageMainMask
