import Proof.Quartic.StageMainMask.RowDimension

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open StageMain

/-- `imp:partition`, `imp:seed` and Step 4 of `sec:algorithm`,
paper/paper.tex: actual division
and remainder operations decode the original center column and projected
sample value into their canonical row, column and pattern codes. -/
def decodeEntryCoordinates : St VV MM :=
  .seq (.op (.dm 32 71 26 25))
    (.seq (.op (.dm 34 35 66 28)) (.op (.dm 66 35 67 27)))

/-- `imp:partition`, `imp:seed` and `prop:time`, paper/paper.tex: the exact numeric decoder
preserves every source field outside its six computed variables. -/
theorem decodeEntryCoordinates_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a)
    (hcol : a.env 32 = r.column.val) (hval : a.env 34 = r.fieldValue.val)
    (hN : a.env 35 = r.selected.1.N)
    (hrow : a.env 71 = 2 ^ PrimT.C4Geo.dRow (entryPointRequest r false false).parameters)
    (hwidth : r.call.n + 4 ≤ C.Wd) :
    Hs C decodeEntryCoordinates a 5 (fun b =>
      b.env 25 = (entryPointRequest r false false).row.val ∧
      b.env 26 = (entryPointRequest r false false).column.val ∧
      b.env 27 = (entryPointRequest r false false).left.val ∧
      b.env 28 = (entryPointRequest r false false).right.val ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [25, 26, 27, 28, 66, 67]) := by
  let hs := Cells.prepare_spec _ r.selected.1 r.selected.2
  let D := PrimT.C4Geo.dRow (entryPointRequest r false false).parameters
  have hk : r.selected.1.k < r.call.n := hs.k_lt_n
  have hn : 0 < r.call.n := hs.n_pos
  have hd : D ≤ r.call.n := by
    dsimp only [D]
    rw [show (entryPointRequest r false false).parameters = Builder.star r.call hs from rfl,
      rowDimension_eq r.call hs]
    omega
  have hrowpos : 0 < a.env 71 := by rw [hrow]; exact Nat.two_pow_pos _
  have hrowfit : 2 * a.env 71 ≤ 2 ^ C.Wd := by
    rw [hrow, ← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by change D + 1 ≤ C.Wd; omega)
  have hNpos : 0 < r.selected.1.N := by rw [hs.N_eq]; exact Nat.two_pow_pos _
  have hNfit : 2 * r.selected.1.N ≤ 2 ^ C.Wd := by
    rw [hs.N_eq, ← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by have := Nat.div_le_self r.selected.1.k 2; omega)
  unfold decodeEntryCoordinates
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_dm C 32 71 26 25 a (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hrowpos hrowfit) ?_
  rintro b rfl
  let b := (a.set 26 (a.env 32 / a.env 71)).set 25 (a.env 32 % a.env 71)
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_dm C 34 35 66 28 b (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simpa (config := {decide := true}) [b, hN] using hNpos)
      (by simpa (config := {decide := true}) [b, hN] using hNfit)) ?_
  rintro d rfl
  let d := (b.set 66 (b.env 34 / b.env 35)).set 28 (b.env 34 % b.env 35)
  refine (hs_dm C 66 35 67 27 d (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simpa (config := {decide := true}) [d, b, hN] using hNpos)
    (by simpa (config := {decide := true}) [d, b, hN] using hNfit)).mono le_rfl ?_
  rintro e rfl
  let e := (d.set 67 (d.env 66 / d.env 35)).set 27 (d.env 66 % d.env 35)
  have hf : Fr a e [25, 26, 27, 28, 66, 67] :=
    (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))))
  refine ⟨?_, ?_, ?_, ?_, rfl, hc.of_fr hf (by decide), hf⟩
  · simp (config := {decide := true}) [d, b, hcol, hrow, entryPointRequest]
  · simp (config := {decide := true}) [d, b, hcol, hrow, entryPointRequest]
  · have he : e.env 27 = (r.fieldValue.val / r.selected.1.N) % r.selected.1.N := by
      simp (config := {decide := true}) [e, d, b, hval, hN]
    exact he.trans (EntryCoordinates.entryPosition_fst_value r).symm
  · have he : e.env 28 = r.fieldValue.val % r.selected.1.N := by
      simp (config := {decide := true}) [e, d, b, hval, hN]
    exact he.trans (EntryCoordinates.entryPosition_snd_value r).symm

end NearQuarticWires.StageMainMask
