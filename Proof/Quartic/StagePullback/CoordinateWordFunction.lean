import Proof.Quartic.StagePullback.CoordinateProgram
import Proof.Gates.Cells.Prelude
import Proof.Gates.Cells.Run
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces

/-- `imp:pullback`, paper/paper.tex: canonical affine
coordinate decoding invokes no external subroutine. -/
noncomputable def coordinateCallee : Callee :=
  ⟨Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    wordFunction_of_wmx (WMX.skip : WMX 1 0) 1 (by decide) (fun _ => 0) (fun e => e.elim)⟩

/-- `prop:time`, paper/paper.tex: the first original
dimension field determines polynomial binary workspace for decoding. -/
def coordinateSizes : Sz := ⟨64, 1, 0, 0, 0, 0⟩

/-- `prop:time`, paper/paper.tex: the physical
workspace is sufficient for every actual scalar in the compact request. -/
theorem coordinateWidth (r : CoordinateRequest) :
    r.point.parameters.n + 4 ≤ coordinateSizes.W (leadOnes r.word) := by
  have hl : leadOnes r.word = natBitLength r.point.parameters.n := by
    unfold CoordinateRequest.word PointRequest.word
    simp only [List.append_assoc]
    exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _
  have hn := lt_natBitLength r.point.parameters.n
  have hp := Nat.one_le_two_pow (n := natBitLength r.point.parameters.n)
  simp only [coordinateSizes, Sz.W, one_mul, hl]
  omega

/-- `imp:pullback`, paper/paper.tex: the complete
coordinate program begins with zero state and initializes its constants. -/
def coordinateColdProgram : St VV MM := .seq initP coordinateProgram

/-- `imp:pullback` and `prop:time`, paper/paper.tex: exact canonical affine decoding runs from the genuine
cold state using only the original scalar request. -/
theorem coordinateCold_run (C : Ctx) (r : CoordinateRequest)
    (hinput : C.inp = r.word) (hwidth : r.point.parameters.n + 4 ≤ C.Wd) :
    Hs C coordinateColdProgram (a0 : DS VV MM) (700 * (r.point.parameters.n + 2))
      (fun b => b.out = r.output) := by
  have htwo : 2 < 2 ^ C.Wd := by
    have hh : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hh ⊢
    omega
  unfold coordinateColdProgram
  refine Hs.mono (Hs.seq (t1 := 5) (t2 := 600 * (r.point.parameters.n + 2))
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl htwo)
    (fun a ⟨hc, _, _, hip, hout, _, _, _, hfr⟩ => ?_)) (by omega) (fun _ h => h)
  have hzero : a.env MarkerCalls.originalCoordinate = 0 := hfr _ (by decide)
  refine Hs.mono (coordinateProgram_run C a r hc hip hzero hinput hwidth) le_rfl ?_
  intro b hb
  simpa only [hout, a0, List.nil_append] using hb

/-- `prop:time`, paper/paper.tex: the native clock
includes actual setup, source-language execution and final head reset. -/
noncomputable def coordinateCost (r : CoordinateRequest) : ℕ :=
  langBudget coordinateCallee coordinateSizes VV MM r.word (700 * (r.point.parameters.n + 2))

/-- `imp:pullback`, paper/paper.tex: a genuine ordinary
cold machine decodes the actual canonical translation and error codes
and returns the exact original-coordinate affine flip bit. -/
noncomputable def coordinateWordFunction :
    WordFunction CoordinateRequest CoordinateRequest.word CoordinateRequest.output coordinateCost :=
  wordFunction_of_lang CoordinateRequest.word CoordinateRequest.output coordinateCallee coordinateSizes
    coordinateColdProgram (fun r => 700 * (r.point.parameters.n + 2)) (by
      intro r
      obtain ⟨b, n, he, hn, hout⟩ := coordinateCold_run
        (ctxOf coordinateCallee coordinateSizes r.word) r rfl (coordinateWidth r)
      exact ⟨b, n, he, hout, hn⟩) (by
      intro r
      have := coordinateWidth r
      omega)

end NearQuarticWires.StagePullback
