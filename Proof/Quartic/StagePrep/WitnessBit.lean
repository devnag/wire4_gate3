import Proof.Gates.Dispatch.Macros
import Proof.Gates.Dispatch.Compile

/-!
# Reading a bounded witness bit

Paper: the witness of `sec:algorithm`, paper/paper.tex,
and `prop:time`. Missing bits are zero; one read does
not inspect the remainder of the witness word.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The one-bit read of the witness in `sec:algorithm`, paper/paper.tex. -/
def readWitnessBit : St VV := .seq (.op (.rdW t0)) (emitB t0)

/-- The read in `sec:algorithm`, paper/paper.tex emits the current bit,
with zero beyond the word, in four language steps. -/
theorem readWitnessBit_spec (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C readWitnessBit a 4 (fun b =>
      b.out = a.out ++ [C.wit.getD a.wq false] ∧
      b.cp = a.cp ∧
      b.wq = (if a.wq < C.wit.length then a.wq + 1 else a.wq) ∧
      Cst b ∧ Fr a b [t0]) := by
  unfold readWitnessBit
  refine Hs.seq (t2 := 2) (hs_rdW C t0 a) ?_
  rintro d rfl
  have hd : Cst
      { a.set t0 (bitOf C.wit a.wq) with
        wq := if a.wq < C.wit.length then a.wq + 1 else a.wq } := by
    exact ⟨by simpa [DS.set, t0, vZ] using hc.z,
      by simpa [DS.set, t0, v1] using hc.one,
      by simpa [DS.set, t0, v2] using hc.two,
      by simpa [DS.set, t0, vPOS] using hc.pos⟩
  refine Hs.mono (emitB_spec t0 (by decide) _ hd) le_rfl ?_
  rintro b ⟨hb, hcp, hwq, henv⟩
  have hbit : decide (bitOf C.wit a.wq = 1) = C.wit.getD a.wq false := by
    unfold bitOf
    cases C.wit.getD a.wq false <;> rfl
  refine ⟨?_, hcp, hwq, ?_, ?_⟩
  · simpa only [DS.set_out, DS.set_env_self, hbit] using hb
  · exact ⟨by rw [henv]; exact hd.z, by rw [henv]; exact hd.one,
      by rw [henv]; exact hd.two, by rw [henv, hcp]; exact hd.pos⟩
  · intro x hx
    rw [henv]
    exact DS.set_env_ne a _ (by simpa using hx)

/-- The framed bit of `sec:algorithm`, paper/paper.tex consists of the
mark and the zero-filled witness bit. -/
def framedWitnessBit : St VV := .seq (.op (.emit true)) readWitnessBit

/-- A marked witness bit, as required by the prefix record in
`sec:algorithm`, paper/paper.tex, costs six language steps. -/
theorem framedWitnessBit_spec (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C framedWitnessBit a 6 (fun b =>
      b.out = a.out ++ [true, C.wit.getD a.wq false] ∧
      b.cp = a.cp ∧
      b.wq = (if a.wq < C.wit.length then a.wq + 1 else a.wq) ∧
      Cst b ∧ Fr a b [t0]) := by
  unfold framedWitnessBit
  refine Hs.seq (t2 := 4) (hs_emit C true a) ?_
  rintro d rfl
  refine Hs.mono (readWitnessBit_spec C _ ⟨hc.z, hc.one, hc.two, hc.pos⟩) le_rfl ?_
  rintro b ⟨hb, hcp, hwq, hconst, hfr⟩
  exact ⟨by simpa only [List.append_assoc, List.cons_append,
    List.nil_append] using hb, hcp, hwq, hconst, hfr⟩

/-- The marked read in `sec:algorithm`, paper/paper.tex is a run of
the physical word program with cost at most `6 * KC C.Wd`. -/
theorem framedWitnessBit_physical (C : Ctx) (inp : List Bool) (p0 cap : ℕ)
    (a : DS VV) (hc : Cst a) (ha : Valid C a)
    (hlay : WitLayout inp p0 C.wit) (hW : 1 ≤ C.Wd)
    (hcw : C.cw.length ≤ C.Wd) (hcapW : 2 * C.Wd + 1 ≤ cap)
    (hcapC : C.cw.length + 1 ≤ cap)
    (hcapI : p0 + 4 * C.wit.length + 4 ≤ cap)
    (hout : a.out.length + 6 ≤ cap) :
    ∃ b, WXExec cap (comp framedWitnessBit) (E C inp p0 a) (E C inp p0 b)
      (6 * KC C.Wd) ∧
      b.out = a.out ++ [true, C.wit.getD a.wq false] ∧
      b.wq ≤ a.wq + 1 ∧ b.cp = a.cp := by
  obtain ⟨b, n, hex, hn, hb, hcp, hwq, _, _⟩ := framedWitnessBit_spec C a hc
  have hrun := (comp_ok C inp p0 cap hlay hW hcw hcapW hcapC hcapI
    hex ha (by omega)).1
  refine ⟨b, WXExec.mono hrun (Nat.mul_le_mul_right _ hn), hb, ?_, hcp⟩
  rw [hwq]
  split_ifs <;> omega

end NearQuarticWires.StagePrep
