import Proof.Quartic.StageColumns.State

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

/-- `imp:partition`, paper/paper.tex: the free-tail
basis column is a unit vector at its computed canonical half-position. -/
def freeProgram : St VV MM :=
  .seq (.op (.copy freePosition columnIndex))
    (.seq (.op (.sub freePosition dataCount))
      (.seq (.op (.add freePosition leftWidth))
        (.ite (.eq coordinateIndex freePosition) (.op (.copy result v1)) (.op (.zero result)))))

/-- `imp:partition` and `prop:time`, paper/paper.tex: the free-tail column position and its literal equality
bit are physically computed, with no supplied coordinate lookup. -/
theorem freeProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams) (j p : ℕ)
    (hi : BitInputs a P j p) (hjN : j ≤ P.n)
    (hfree : P.r / 2 * PrimT.C4Geo.dB P ≤ j) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C freeProgram a 10 (fun b =>
      b.env result = (p == P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P)).toNat ∧
      b.sh = a.sh ∧ Fr a b [freePosition, result, vJ]) := by
  have hleft : P.r / 2 * P.b ≤ P.n :=
    (Nat.mul_le_mul_right P.b (Nat.div_le_self P.r 2)).trans P.r_mul_b_le
  have hsmall := StageHamming.scalar_word_bound P C.Wd hwidth
  unfold freeProgram
  refine Hx.hs (Hs.then (hs_copy C freePosition columnIndex a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set freePosition (a.env columnIndex)
  refine Hs.then (hs_sub C freePosition dataCount a1 (by decide)
    (by vsimp [a1, hi.column, hi.count]; exact hfree))
    (fun b hb n2 hn2 => ?_)
  subst hb
  let a2 := a1.set freePosition (a1.env freePosition - a1.env dataCount)
  refine Hs.then (hs_add C freePosition leftWidth a2 (by decide)
    (by vsimp [a2, a1, hi.column, hi.count, hi.left]; omega))
    (fun b hb n3 hn3 => ?_)
  subst hb
  let a3 := a2.set freePosition (a2.env freePosition + a2.env leftWidth)
  have hf3 : Fr a a3 [freePosition, result, vJ] :=
    (Fr.set a _ (by decide)).trans ((Fr.set a1 _ (by decide)).trans
      (Fr.set a2 _ (by decide)))
  have hc3 : Cst a3 := hi.constants.of_fr hf3 (by decide)
  have hpos : a3.env freePosition =
      P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P) := by
    vsimp [a3, a2, a1, hi.column, hi.count, hi.left]
    omega
  have hp3 : a3.env coordinateIndex = p := (hf3 _ (by decide)).trans hi.coordinate
  refine Hs.last (Hs.ite (t := 1)
    (R := fun b => b.env result =
      (p == P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P)).toNat ∧
      b.sh = a3.sh ∧ Fr a3 b [freePosition, result, vJ])
    (show coordinateIndex ≠ freePosition by decide)
    (fun he => ?_) (fun he => ?_)) ?_
  · refine (hs_copy C result v1 a3 (by decide)).mono le_rfl ?_
    rintro b rfl
    have hraw : a3.env coordinateIndex = a3.env freePosition := of_decide_eq_true he
    have heq : p = P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P) := by
      exact hp3.symm.trans (hraw.trans hpos)
    exact ⟨by simp [hc3.one, heq], rfl, Fr.set a3 _ (by decide)⟩
  · refine (hs_zero C result a3).mono le_rfl ?_
    rintro b rfl
    have hraw : a3.env coordinateIndex ≠ a3.env freePosition := of_decide_eq_false he
    have heq : p ≠ P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P) := by
      intro h
      exact hraw (hp3.trans (h.trans hpos.symm))
    have hbeq : (p == P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P)) = false :=
      beq_eq_false_iff_ne.mpr heq
    exact ⟨by simp [hbeq], rfl, Fr.set a3 _ (by decide)⟩
  · rintro b ⟨hv, hsh, hfr⟩ n4 hn4
    exact ⟨⟨hv, hsh, hf3.trans hfr⟩, by omega⟩

end NearQuarticWires.StageColumns
