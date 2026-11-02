import Proof.Quartic.StagePrep.WitnessPrefix
import Proof.Gates.Codec.PairFrame

/-!
# The physical prefix reader

Paper: `sec:algorithm`, paper/paper.tex, and
`prop:time`. The read count, rather than the length
of the witness word, bounds the execution.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.RepairOrdinary

/-- The framed prefix computation of `sec:algorithm`, paper/paper.tex. -/
def prefixReader : St VV :=
  .seq (.op (.zero prefixIndex)) (.seq prefixLoop (.op (.emit false)))

/-- The reader of `sec:algorithm`, paper/paper.tex writes exactly a
frame of the prescribed number of zero-filled witness bits. -/
theorem prefixReader_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (l : ℕ) (hlimit : a.env prefixLimit = l) (hwq : a.wq = 0)
    (hl : l < 2 ^ C.Wd) :
    Hs C prefixReader a (10 * l + 6) (fun b =>
      b.out = a.out ++ frame (prefixBits C.wit l) ∧
      b.cp = a.cp ∧ b.wq = min l C.wit.length ∧
      b.env prefixIndex = l ∧ b.env prefixLimit = l ∧ Cst b ∧
      Fr a b [t0, prefixIndex]) := by
  unfold prefixReader
  refine Hs.mono (Hs.seq (t2 := 10 * l + 4) (hs_zero C prefixIndex a) ?_)
    (by omega) (fun _ h => h)
  rintro d rfl
  have hd : Cst (a.set prefixIndex 0) :=
    ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩
  refine Hs.seq (t2 := 1) (prefixLoop_spec C _ hd l (by simp)
    (by rw [DS.set_env_ne _ _ (by decide)]; exact hlimit) hwq hl) ?_
  rintro b ⟨hbout, hbcp, hbwq, hbi, hbl, hbc, hbfr⟩
  refine Hs.mono (hs_emit C false b) le_rfl ?_
  rintro e rfl
  refine ⟨?_, hbcp, hbwq, hbi, hbl,
    ⟨hbc.z, hbc.one, hbc.two, hbc.pos⟩,
    Fr.trans (Fr.set a _ (by decide)) hbfr⟩
  rw [hbout]
  simp only [DS.set_out, List.append_assoc]
  congr 1
  rw [NearCubicGates.Close.Codec.frame_eq_marks]
  congr 1

/-- The bounded prefix computation in `sec:algorithm`, paper/paper.tex executes on physical word tapes in at most
`(10*l+6) * KC C.Wd` steps, independent of the witness suffix. -/
theorem prefixReader_physical (C : Ctx) (inp : List Bool) (p0 cap : ℕ)
    (a : DS VV) (hc : Cst a) (ha : Valid C a) (l : ℕ)
    (hlimit : a.env prefixLimit = l) (hwq : a.wq = 0)
    (hl : l < 2 ^ C.Wd) (hlay : WitLayout inp p0 C.wit)
    (hW : 1 ≤ C.Wd) (hcw : C.cw.length ≤ C.Wd)
    (hcapW : 2 * C.Wd + 1 ≤ cap) (hcapC : C.cw.length + 1 ≤ cap)
    (hcapI : p0 + 4 * C.wit.length + 4 ≤ cap)
    (hout : a.out.length + (10 * l + 6) ≤ cap) :
    ∃ b, WXExec cap (comp prefixReader) (E C inp p0 a) (E C inp p0 b)
        ((10 * l + 6) * KC C.Wd) ∧
      b.out = a.out ++ frame (prefixBits C.wit l) ∧
      b.wq = min l C.wit.length ∧ b.cp = a.cp := by
  obtain ⟨b, n, hex, hn, hbout, hbcp, hbwq, _, _, _, _⟩ :=
    prefixReader_spec C a hc l hlimit hwq hl
  have hrun := (comp_ok C inp p0 cap hlay hW hcw hcapW hcapC hcapI
    hex ha (by omega)).1
  exact ⟨b, WXExec.mono hrun (Nat.mul_le_mul_right _ hn), hbout, hbwq, hbcp⟩

end NearQuarticWires.StagePrep
