import Proof.Quartic.StageColumns.State

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

/-- `imp:partition`, paper/paper.tex: a data-column
bit vanishes outside its actual block, and otherwise uses the literal
canonical data-position and parity computations. -/
def blockProgram : St VV MM :=
  .seq divisionProgram (.ite (.eq coordinateBlock columnBlock)
    codewordProgram (.op (.zero result)))

/-- `imp:partition` and `prop:time`, paper/paper.tex: actual scalar divisions and block comparison produce
the exact canonical data-column contribution. -/
theorem blockProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams) (j p : ℕ)
    (hi : BitInputs a P j p) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C blockProgram a
      (P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) + 70) (fun b =>
        b.env result = ((p / P.b == j / PrimT.C4Geo.dB P) &&
          PrimT.C4Geo.cwBit P (PrimT.C4Geo.dpos P (j % PrimT.C4Geo.dB P)) (p % P.b)).toNat ∧
        b.sh = a.sh ∧ Fr a b bitScratch) := by
  unfold blockProgram
  refine Hx.hs (Hs.then (divisionProgram_run C a P j p
    hi.column hi.coordinate hi.data hi.blockWidth hwidth)
    (fun b ⟨hbj, hbm, hbp, hbq, hbsh, hbfr⟩ n1 hn1 => ?_))
  have hfb : Fr a b bitScratch := hbfr.weaken (by
    intro y hy
    exact List.mem_append_left _ (List.mem_append_left _ hy))
  have hbi := hi.frame hfb
  refine Hs.last (Hs.ite
    (t := P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) + 60)
    (R := fun d => d.env result = ((p / P.b == j / PrimT.C4Geo.dB P) &&
      PrimT.C4Geo.cwBit P (PrimT.C4Geo.dpos P (j % PrimT.C4Geo.dB P)) (p % P.b)).toNat ∧
      d.sh = b.sh ∧ Fr b d bitScratch)
    (show coordinateBlock ≠ columnBlock by decide) (fun he => ?_) (fun he => ?_)) ?_
  · have heq : p / P.b = j / PrimT.C4Geo.dB P := by
      simpa only [Cnd.eval, hbp, hbj, decide_eq_true_eq] using he
    refine (codewordProgram_run C b hbi.constants P (j % PrimT.C4Geo.dB P) (p % P.b)
      hbi.blockWidth hbi.parityWidth hbm hbq
      (Nat.mod_lt _ (PrimT.C4Geo.dB_pos P)) (Nat.mod_lt _ P.b_pos) hwidth).mono le_rfl ?_
    rintro d ⟨hdv, hdsh, hdfr⟩
    refine ⟨?_, hdsh, hdfr.weaken (by
      intro y hy
      exact List.mem_append_left _ (List.mem_append_right _ hy))⟩
    simpa only [heq, beq_self_eq_true, Bool.true_and] using hdv
  · have heq : p / P.b ≠ j / PrimT.C4Geo.dB P := by
      simpa only [Cnd.eval, hbp, hbj, decide_eq_false_iff_not] using he
    have hbeq : (p / P.b == j / PrimT.C4Geo.dB P) = false := beq_eq_false_iff_ne.mpr heq
    refine (hs_zero C result b).mono (by omega) ?_
    rintro d rfl
    exact ⟨by simp [hbeq], rfl, Fr.set b _ (by decide)⟩
  · rintro d ⟨hdv, hdsh, hdfr⟩ n2 hn2
    exact ⟨⟨hdv, hdsh.trans hbsh, hfb.trans hdfr⟩, by omega⟩

end NearQuarticWires.StageColumns
