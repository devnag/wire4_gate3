import Proof.Quartic.StageMainMask.PointStep

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePullback

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: every original coordinate is physically
computed and packed, using only the retained actual scalar metadata. -/
def packActualPoint : St VV MM :=
  .seq (.op (.zero packedPointRegister))
    (.seq (.op (.copy packedPointPower v1))
      (forS MarkerCalls.originalCoordinate 20 pointPackingStep))

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: the complete coordinate loop
returns the exact original point word, preserving all source data and
charging the canonical encoder once per actual coordinate. -/
theorem packActualPoint_run (C : Ctx) (q : PointRequest) (a : DS VV MM)
    (hi : PointData a q) (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C packActualPoint a
      (q.parameters.n * (500 * (q.parameters.n + 1) ^ 3 + 9) + 8) (fun b =>
        b.env packedPointRegister = q.packed ∧ PointData b q ∧ b.sh = a.sh ∧
        Fr a b pointPackingScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env packedPointRegister = pointPrefix q k ∧ b.env packedPointPower = 2 ^ k ∧
    PointData b q ∧ b.sh = a.sh ∧ Fr a b pointPackingScratch
  have hcoordmem : MarkerCalls.originalCoordinate ∈ pointPackingScratch := by decide
  have hI : ∀ k b value, I k b → I k (b.set MarkerCalls.originalCoordinate value) := by
    rintro k b value ⟨hbv, hbp, hbi, hbsh, hbfr⟩
    have hf : Fr b (b.set MarkerCalls.originalCoordinate value) pointPackingScratch :=
      Fr.set b _ hcoordmem
    exact ⟨(DS.set_env_ne _ _ (by decide)).trans hbv,
      (DS.set_env_ne _ _ (by decide)).trans hbp, hbi.framePacking hf, hbsh, hbfr.trans hf⟩
  have hbody : ∀ k < q.parameters.n, ∀ b, I k b →
      b.env MarkerCalls.originalCoordinate = k → b.env 20 = q.parameters.n →
      Hs C pointPackingStep b (500 * (q.parameters.n + 1) ^ 3 + 5) (fun d =>
        I (k + 1) d ∧ d.env MarkerCalls.originalCoordinate = k ∧ d.env 20 = q.parameters.n) := by
    rintro k hk b ⟨hbv, hbp, hbi, hbsh, hbfr⟩ hbcoord hbn
    refine (pointPackingStep_run C q k hk b hbi hbcoord hbv hbp hwidth).mono le_rfl ?_
    rintro d ⟨hdv, hdp, hdi, hdsh, hdcoord, hdfr⟩
    have hcoord : d.env MarkerCalls.originalCoordinate = k := hdcoord.trans hbcoord
    refine ⟨⟨hdv, hdp, hdi, hdsh.trans hbsh, hbfr.trans hdfr⟩, hcoord, ?_⟩
    simpa [VV, pointFieldRegister, PointRequest.fields] using hdi.fields 0
  have hn : a.env 20 = q.parameters.n := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hi.fields 0
  have hfit : q.parameters.n < 2 ^ C.Wd :=
    (Nat.lt_two_pow_self (n := q.parameters.n)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  unfold packActualPoint
  refine (Hs.seq (t1 := 1)
    (t2 := q.parameters.n * (500 * (q.parameters.n + 1) ^ 3 + 9) + 6)
    (hs_zero C packedPointRegister a) ?_).mono (by omega) (fun _ h => h)
  rintro b rfl
  let b := a.set packedPointRegister 0
  have hbf : Fr a b pointPackingScratch := Fr.set a _ (by decide)
  have hbi : PointData b q := hi.framePacking hbf
  refine (Hs.seq (t1 := 1)
    (t2 := q.parameters.n * (500 * (q.parameters.n + 1) ^ 3 + 9) + 4)
    (hs_copy C packedPointPower v1 b (by decide)) ?_).mono (by omega) (fun _ h => h)
  rintro c rfl
  let c := b.set packedPointPower (b.env v1)
  have hcf : Fr b c pointPackingScratch := Fr.set b _ (by decide)
  have hci : PointData c q := hbi.framePacking hcf
  have h0 : I 0 c := by
    exact ⟨by
      change (b.set packedPointPower (b.env v1)).env packedPointRegister = _
      rw [DS.set_env_ne _ _ (by decide : packedPointRegister ≠ packedPointPower)]
      exact (DS.set_env_self _ _ _).trans (pointPrefix_zero q).symm,
      by simp [c, hbi.constants.one], hci, rfl,
      hbf.trans hcf⟩
  have hcn : c.env 20 = q.parameters.n := (hcf _ (by decide)).trans ((hbf _ (by decide)).trans hn)
  refine (forS_spec' (C := C) MarkerCalls.originalCoordinate 20 (by decide) pointPackingStep
    c q.parameters.n hfit I (500 * (q.parameters.n + 1) ^ 3 + 5) hI h0 hcn hbody).mono
      (by ring_nf; omega) ?_
  rintro d ⟨⟨hdv, _hdp, hdi, hdsh, hdfr⟩, _hdcoord, _hdn⟩
  exact ⟨hdv.trans (pointPrefix_full q), hdi, hdsh, hdfr⟩

end NearQuarticWires.StageMainMask
