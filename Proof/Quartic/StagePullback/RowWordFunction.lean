import Proof.Quartic.StagePullback.RowExecution
import Proof.Quartic.StagePullback.CoordinateWordFunction

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the original
dimension field determines a fixed polynomial binary workspace, covering
all actual original child coefficients and their exact affine target. -/
def rowSizes : Sz := ⟨256, 4, 0, 0, 0, 0⟩

/-- `imp:pullback`, paper/paper.tex: the first scalar
source field of every original row request is its original dimension. -/
theorem RowRequest.leading_ones (r : RowRequest) : leadOnes r.word = natBitLength r.parameters.n := by
  unfold RowRequest.word RowRequest.fields
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

/-- `prop:time`, paper/paper.tex: the actual input
field bound from the original compiler covers every native binary
operation in the complete affine row program. -/
theorem rowWidth (r : RowRequest) :
    r.Lout + 4 ≤ rowSizes.W (leadOnes r.word) := by
  have hV : 1 ≤ r.parameters.n + 1 := by omega
  have h2 : (r.parameters.n + 1) ^ 2 ≤ (r.parameters.n + 1) ^ 4 :=
    Nat.pow_le_pow_right hV (by decide)
  have h1 : r.parameters.n + 1 ≤ (r.parameters.n + 1) ^ 4 :=
    Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) _
  have h0 : 1 ≤ (r.parameters.n + 1) ^ 4 := Nat.one_le_pow _ _ hV
  have hbound : r.Lout + 4 ≤ 256 * (r.parameters.n + 1) ^ 4 := by
    unfold RowRequest.Lout
    nlinarith only [r.Lin_le, h2, h1, h0]
  have hn : r.parameters.n + 1 ≤ 2 ^ natBitLength r.parameters.n := lt_natBitLength _
  have hp := Nat.pow_le_pow_left hn 4
  have he : 2 ^ (4 * natBitLength r.parameters.n) = (2 ^ natBitLength r.parameters.n) ^ 4 := by
    rw [← pow_mul, Nat.mul_comm]
  simp only [rowSizes, Sz.W, r.leading_ones, he]
  exact hbound.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 256 hp)

/-- `imp:pullback`, paper/paper.tex: the actual
original-row compiler begins from the genuine zero state and initializes
its arithmetic constants before reading any source field. -/
def rowColdProgram : St VV MM := .seq initP rowProgram

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the original signed child row and actual canonical scalar
metadata alone physically produce its complete signed native pullback
from the cold state, with all source acquisition paid. -/
theorem rowCold_run (C : Ctx) (r : RowRequest) (hinput : C.inp = r.word)
    (hwidth : r.Lout + 4 ≤ C.Wd) :
    Hs C rowColdProgram (a0 : DS VV MM) (r.sourceClock + 6) (fun b => b.out = r.output) := by
  have htwo : 2 < 2 ^ C.Wd := by
    have hh : 4 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (n := 2) (by decide)
      (show 2 ≤ C.Wd by omega)
    omega
  unfold rowColdProgram
  refine Hs.mono (Hs.seq (t1 := 5) (t2 := r.sourceClock)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl htwo)
    (fun a ⟨hc, hram, hrc, hip, hout, _, _, _, hfr⟩ => ?_)) (by omega) (fun _ h => h)
  have hzero : a.env MarkerCalls.originalCoordinate = 0 := hfr _ (by decide)
  have hp0 : a.env SignedCoefficients.positive = 0 := hfr _ (by decide)
  have hn0 : a.env SignedCoefficients.negative = 0 := hfr _ (by decide)
  refine Hs.mono (rowProgram_run C a r hc hip hzero hp0 hn0
    (by rw [hram]; rfl) (by rw [hram]; rfl) (by rw [hrc]; rfl) (by rw [hrc]; rfl)
    hinput hwidth) le_rfl ?_
  intro b hb
  simpa only [hout, a0, List.nil_append] using hb

/-- `prop:time`, paper/paper.tex: the native row
clock includes actual physical setup, every original input bit, signed
arithmetic, native serialization and final machine head reset. -/
noncomputable def rowCost (r : RowRequest) : ℕ :=
  langBudget coordinateCallee rowSizes VV MM r.word (r.sourceClock + 6)

/-- `imp:pullback` and `lem:print`, paper/paper.tex: a genuine ordinary cold machine transforms the ORIGINAL
signed child fields and actual canonical metadata into the exact native
affine row's signed field stream. -/
noncomputable def rowWordFunction : WordFunction RowRequest RowRequest.word RowRequest.output rowCost :=
  wordFunction_of_lang RowRequest.word RowRequest.output coordinateCallee rowSizes rowColdProgram
    (fun r => r.sourceClock + 6) (by
      intro r
      obtain ⟨b, n, he, hn, hout⟩ := rowCold_run
        (ctxOf coordinateCallee rowSizes r.word) r rfl (rowWidth r)
      exact ⟨b, n, he, hout, hn⟩) (by
      intro r
      have := rowWidth r
      omega)

end NearQuarticWires.StagePullback
