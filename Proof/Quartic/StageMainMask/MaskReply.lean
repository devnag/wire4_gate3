import Proof.Quartic.StageMainMask.ReplyData
import Proof.Quartic.StageMainMask.EntryValues

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `def:mask`, paper/paper.tex: an actual
integer comparison against the selected cutoff is conjoined with
the actual structural reply; equality at the cutoff is accepted. -/
def compareMask : St VV MM := .seq (.op (.zero numericMaskValue))
  (.ite (.eq structuralFlag v1)
    (.ite (.lt 36 populationValue) skipS (.op (.copy numericMaskValue v1))) skipS)

/-- `def:mask` and `prop:time`, paper/paper.tex: the actual integer cutoff and Boolean conjunction
require a constant physical clock and preserve all original sources. -/
theorem compareMask_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (bit : Bool) (population cutoff : ℕ)
    (hs : a.env structuralFlag = bit.toNat) (hp : a.env populationValue = population)
    (ht : a.env 36 = cutoff) :
    Hs C compareMask a 5 (fun b =>
      b.env numericMaskValue = (bit && decide (population ≤ cutoff)).toNat ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [numericMaskValue, vJ]) := by
  unfold compareMask
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_zero C numericMaskValue a) ?_
  rintro b rfl
  let b := a.set numericMaskValue 0
  have hf : Fr a b [numericMaskValue, vJ] := Fr.set a _ (by simp)
  have hbc := Cst.of_fr hc hf (by decide)
  have hbs : b.env structuralFlag = bit.toNat := (hf _ (by decide)).trans hs
  have hbp : b.env populationValue = population := (hf _ (by decide)).trans hp
  have hbt : b.env 36 = cutoff := (hf _ (by decide)).trans ht
  have hbz : b.env numericMaskValue = 0 := DS.set_env_self _ _ _
  cases bit with
  | false =>
    refine (Hs.iteF (by change structuralFlag ≠ v1; decide)
      (by change decide (b.env structuralFlag = b.env v1) = _; rw [hbs, hbc.one]; rfl) (skip_spec b)).mono (by omega) ?_
    rintro d rfl
    have hdf : Fr b (b.set vJ 0) [numericMaskValue, vJ] := Fr.set b _ (by simp)
    exact ⟨by simpa only [Bool.false_and, Bool.toNat_false] using (DS.set_env_ne b 0 (by decide : numericMaskValue ≠ vJ)).trans hbz,
      rfl, Cst.of_fr hbc hdf (by decide), hf.trans hdf⟩
  | true =>
    refine Hs.iteT (by change structuralFlag ≠ v1; decide)
      (by change decide (b.env structuralFlag = b.env v1) = _; rw [hbs, hbc.one]; rfl) ?_
    by_cases h : cutoff < population
    · refine Hs.iteT (by change (36 : Fin VV) ≠ populationValue; decide)
        (by change decide (b.env 36 < b.env populationValue) = _; rw [hbt, hbp]; exact decide_eq_true h) ((skip_spec b).mono le_rfl ?_)
      rintro d rfl
      have hdf : Fr b (b.set vJ 0) [numericMaskValue, vJ] := Fr.set b _ (by simp)
      exact ⟨by simpa only [Bool.true_and, decide_eq_false (by omega : ¬population ≤ cutoff),
          Bool.toNat_false] using (DS.set_env_ne b 0 (by decide : numericMaskValue ≠ vJ)).trans hbz,
        rfl, Cst.of_fr hbc hdf (by decide), hf.trans hdf⟩
    · refine Hs.iteF (by change (36 : Fin VV) ≠ populationValue; decide)
        (by change decide (b.env 36 < b.env populationValue) = _; rw [hbt, hbp]; exact decide_eq_false h)
        ((hs_copy C numericMaskValue v1 b (by decide)).mono le_rfl ?_)
      rintro d rfl
      have hdf : Fr b (b.set numericMaskValue (b.env v1)) [numericMaskValue, vJ] := Fr.set b _ (by simp)
      exact ⟨by simp [hbc.one, show population ≤ cutoff by omega],
        rfl, Cst.of_fr hbc hdf (by decide), hf.trans hdf⟩

end NearQuarticWires.StageMainMask
