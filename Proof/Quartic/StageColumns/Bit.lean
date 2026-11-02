import Proof.Quartic.StageColumns.Block
import Proof.Quartic.StageColumns.Free

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

/-- `imp:partition`, paper/paper.tex: literal
comparisons select the original block-column or free unit-vector
case of the canonical generator. -/
def bitProgram : St VV MM :=
  .ite (.lt columnIndex dataCount)
    (.ite (.lt coordinateIndex leftWidth) blockProgram (.op (.zero result))) freeProgram

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: actual scalar parameters
compute the exact common-generator column bit, with all data-position,
parity, division, comparison and initialization operations paid. -/
theorem bitProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams) (j p : ℕ)
    (hi : BitInputs a P j p) (hj : j < PrimT.C4Geo.dRow P)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C bitProgram a (bitClock P) (fun b =>
      b.env result = (PrimT.C4Geo.colBit P j p).toNat ∧
      b.sh = a.sh ∧ Fr a b bitScratch) := by
  unfold bitProgram bitClock
  refine Hs.ite (t := P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) + 199)
    (show columnIndex ≠ dataCount by decide) (fun he => ?_) (fun he => ?_)
  · have hdata : j < P.r / 2 * PrimT.C4Geo.dB P := by
      simpa only [Cnd.eval, hi.column, hi.count, decide_eq_true_eq] using he
    refine Hs.ite (t := P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) + 198)
      (show coordinateIndex ≠ leftWidth by decide) (fun hp => ?_) (fun hp => ?_)
    · have hcoord : p < P.r / 2 * P.b := by
        simpa only [Cnd.eval, hi.coordinate, hi.left, decide_eq_true_eq] using hp
      refine (blockProgram_run C a P j p hi hwidth).mono (by omega) ?_
      rintro b ⟨hbv, hbsh, hbfr⟩
      exact ⟨by simpa [PrimT.C4Geo.colBit, hdata, hcoord] using hbv, hbsh, hbfr⟩
    · have hcoord : ¬ p < P.r / 2 * P.b := by
        simpa only [Cnd.eval, hi.coordinate, hi.left, decide_eq_false_iff_not] using hp
      refine (hs_zero C result a).mono (by omega) ?_
      rintro b rfl
      exact ⟨by simp [PrimT.C4Geo.colBit, hdata, hcoord], rfl, Fr.set a _ (by decide)⟩
  · have hdata : ¬ j < P.r / 2 * PrimT.C4Geo.dB P := by
      simpa only [Cnd.eval, hi.column, hi.count, decide_eq_false_iff_not] using he
    have hjN : j ≤ P.n := hj.le.trans (dimensions_le P).2
    refine (freeProgram_run C a P j p hi hjN (by omega) hwidth).mono (by omega) ?_
    rintro b ⟨hbv, hbsh, hbfr⟩
    refine ⟨?_, hbsh, hbfr.weaken (by intro y hy; exact List.mem_append_right _ hy)⟩
    simpa only [PrimT.C4Geo.colBit, if_neg hdata] using hbv

end NearQuarticWires.StageColumns
