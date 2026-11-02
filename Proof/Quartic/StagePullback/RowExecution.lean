import Proof.Quartic.StagePullback.RowPrepared
import Proof.Quartic.StagePullback.FinalTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms
open NativeRows

/-- `imp:pullback` and `lem:print`, paper/paper.tex: exact source clock for original row decoding, affine
transformation and complete signed native output. -/
def RowRequest.sourceClock (r : RowRequest) : ℕ :=
  500 * (r.Lout + 2) +
    (r.parameters.n * (10 * r.Lin + 21 * r.parameters.n + 204) + 4) +
    (10 * r.Lin + 40) +
    (2 * PrimT.C4Geo.width r.parameters * (12 * r.Lout + 20) + 12 * r.Lout + 50) + 3

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the complete original-source affine row compiler is
literal setup, original coefficient iteration, exact original-target
assembly and actual native signed output. -/
def rowProgram : St VV MM :=
  .seq rowSetupProgram (.seq NativeRows.rowProgram
    (.seq SignedCoefficients.originalTargetProgram rowsOutputProgram))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: original scalar metadata and the original signed child
body alone physically produce the complete canonical native affine row,
including transposition, zero padding and the exact adjusted target. -/
theorem rowProgram_run (C : Ctx) (a : DS VV MM) (r : RowRequest)
    (hc : Cst a) (hip : a.ip = 0) (hzero : a.env MarkerCalls.originalCoordinate = 0)
    (hp0 : a.env SignedCoefficients.positive = 0) (hn0 : a.env SignedCoefficients.negative = 0)
    (hleft0 : a.ram leftStore = []) (hright0 : a.ram rightStore = [])
    (hlc0 : a.rc leftStore = 0) (hrc0 : a.rc rightStore = 0)
    (hinput : C.inp = r.word) (hwidth : r.Lout + 4 ≤ C.Wd) :
    Hs C rowProgram a r.sourceClock (fun b => b.out = a.out ++ r.output) := by
  have hdim : r.parameters.n + 4 ≤ C.Wd := by unfold RowRequest.Lout at hwidth; omega
  have hLin : r.Lin + 1 ≤ C.Wd := by unfold RowRequest.Lout at hwidth; omega
  have hloop : r.Lin + r.parameters.n + 6 ≤ C.Wd := by unfold RowRequest.Lout at hwidth; omega
  unfold rowProgram
  refine Hx.hs (Hs.then (rowSetup_run C a r hc hip hzero hp0 hn0 hinput hwidth)
    (fun b ⟨hb, hbip, hbrest⟩ n1 hn1 => ?_))
  have hbram : b.ram = a.ram := congrArg (fun v => v.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun v => v.2.2.1) hbrest
  have hbout : b.out = a.out := congrArg Prod.fst hbrest
  have hb0 : b.ram leftStore = [] := by rw [hbram]; exact hleft0
  have hb1 : b.ram rightStore = [] := by rw [hbram]; exact hright0
  have hbc0 : b.rc leftStore = 0 := by rw [hbrc]; exact hlc0
  have hbc1 : b.rc rightStore = 0 := by rw [hbrc]; exact hrc0
  have hb20 : b.env 20 = r.parameters.n := by
    simpa [VV, rowFieldRegister, RowRequest.fields] using hb.stored.fields 0
  have hbLin : b.env fieldWidth = r.Lin := by
    simpa [VV, rowFieldRegister, RowRequest.fields] using hb.stored.fields 1
  have hbLout : b.env FieldOutput.width = r.Lout := by
    simpa [VV, rowFieldRegister, RowRequest.fields] using hb.stored.fields 2
  have hbody : C.inp.drop b.ip = r.body := by
    rw [hinput, hbip, ← List.drop_drop]
    simp [RowRequest.word]
  have hbody' : C.inp.drop b.ip = (List.ofFn r.child.weight).flatMap
      (fun z => binary r.Lin (SInt.encS z)) ++ binary r.Lin (SInt.encS r.child.target) := by
    simpa only [RowRequest.body, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using hbody
  refine Hs.then (NativeRows.rowProgram_run C b r.point r.child r.transpose r.Lin
    (binary r.Lin (SInt.encS r.child.target)) hb.inputs hloop hb20 hbLin r.weightsFit hbody'
    hb.leftEnd hb.blockedEnd hb.freeLeftEnd hb.stored.transpose hb0 hb1 hbc0 hbc1
    hb.stored.positive hb.stored.negative)
    (fun c ⟨hrow, _, _⟩ n2 hn2 => ?_)
  have hcc : Cst c := hb.stored.constants.of_fr hrow.frame (by decide)
  have hcLin : c.env fieldWidth = r.Lin := (hrow.frame _ (by decide)).trans hbLin
  have hcLout : c.env FieldOutput.width = r.Lout := (hrow.frame _ (by decide)).trans hbLout
  have hcw : c.env nativeWidth = PrimT.C4Geo.width r.parameters := (hrow.frame _ (by decide)).trans hb.width
  have hcCntL : c.env leftCount = (rowNumbers r.point r.child r.transpose true r.parameters.n).length :=
    (hrow.frame _ (by decide)).trans hb.leftCount
  have hcCntR : c.env rightCount = (rowNumbers r.point r.child r.transpose false r.parameters.n).length :=
    (hrow.frame _ (by decide)).trans hb.rightCount
  have hcinput : C.inp.drop c.ip = binary r.Lin (SInt.encS r.child.target) ++ [] := by
    have hh := hrow.source
    dsimp only [RowRequest.point] at hh
    rw [List.drop_eq_nil_of_le (as := List.ofFn r.child.weight) (i := r.parameters.n) (by simp)] at hh
    simpa using hh
  have htAbs : r.child.target.natAbs ≤ 2 ^ r.Lin := by
    have ht := r.targetFits
    unfold SInt.encS at ht
    split_ifs at ht <;> omega
  have hmass : c.env SignedCoefficients.positive + c.env SignedCoefficients.negative +
      r.child.target.natAbs ≤ (r.parameters.n + 1) * 2 ^ r.Lin := by
    rw [hrow.mass]
    have hh := massPrefix_le r.point r.child r.Lin r.parameters.n le_rfl r.weightsFit
    calc
      _ ≤ r.parameters.n * 2 ^ r.Lin + 2 ^ r.Lin := Nat.add_le_add hh htAbs
      _ = _ := by ring
  have hmassLt : c.env SignedCoefficients.positive + c.env SignedCoefficients.negative +
      r.child.target.natAbs < 2 ^ (r.Lin + r.parameters.n + 6) :=
    hmass.trans_lt (rowAccumulatorWidth { C with Wd := r.Lin + r.parameters.n + 6 }
      r.parameters.n r.Lin le_rfl)
  have htargetFit : 2 * (c.env SignedCoefficients.positive + c.env SignedCoefficients.negative +
      r.child.target.natAbs) + 1 < 2 ^ C.Wd := by
    have hp : 2 * 2 ^ (r.Lin + r.parameters.n + 6) ≤ 2 ^ C.Wd := by
      rw [Nat.mul_comm 2, ← pow_succ]
      exact Nat.pow_le_pow_right (by decide) (by unfold RowRequest.Lout at hwidth; omega)
    omega
  refine Hs.then (SignedCoefficients.originalTargetProgram_run_frame C c hcc r.child.target r.Lin []
    (by omega) hcLin hLin r.targetFits hcinput htargetFit)
    (fun d ⟨hdv, _, _, hdout, hdram, hdrc, hdc, hdfr⟩ n3 hn3 => ?_)
  have hdl : d.env FieldOutput.width = r.Lout := (hdfr _ (by decide)).trans hcLout
  have hdw : d.env nativeWidth = PrimT.C4Geo.width r.parameters := (hdfr _ (by decide)).trans hcw
  have hdcl : d.env leftCount = (rowNumbers r.point r.child r.transpose true r.parameters.n).length :=
    (hdfr _ (by decide)).trans hcCntL
  have hdcr : d.env rightCount = (rowNumbers r.point r.child r.transpose false r.parameters.n).length :=
    (hdfr _ (by decide)).trans hcCntR
  have hdt : d.env SignedCoefficients.value =
      SInt.encS (r.child.target - targetPrefix r.point r.child r.parameters.n) := by
    rw [hdv, hrow.difference]
    congr 1
    dsimp only [RowRequest.point]
    ring
  have hdL : d.ram leftStore = rowNumbers r.point r.child r.transpose true r.parameters.n := by
    rw [hdram]
    exact hrow.left
  have hdR : d.ram rightStore = rowNumbers r.point r.child r.transpose false r.parameters.n := by
    rw [hdram]
    exact hrow.right
  have hdcL : d.rc leftStore = (rowNumbers r.point r.child r.transpose true r.parameters.n).length := by
    rw [hdrc]
    exact hrow.leftCursor
  have hdcR : d.rc rightStore = (rowNumbers r.point r.child r.transpose false r.parameters.n).length := by
    rw [hdrc]
    exact hrow.rightCursor
  have hnf : PrimT.C4Geo.width r.parameters < 2 ^ C.Wd :=
    (nativeWidth_le r.parameters).trans_lt (Flips.markerWidth C r.parameters hdim).2.2.2
  have hlf : r.Lout < 2 ^ C.Wd :=
    (show r.Lout < C.Wd by omega).trans (Nat.lt_two_pow_self (n := C.Wd))
  refine Hs.last (rowsOutputProgram_run C d hdc
    (rowNumbers r.point r.child r.transpose true r.parameters.n)
    (rowNumbers r.point r.child r.transpose false r.parameters.n)
    (PrimT.C4Geo.width r.parameters) r.Lout hdL hdR hdcL hdcR hdcl hdcr hdw hdl
    (rowNumbers_length_le r.point r.child r.transpose true)
    (rowNumbers_length_le r.point r.child r.transpose false) hnf hlf (by omega)) ?_
  rintro e he n4 hn4
  refine ⟨?_, ?_⟩
  · rw [he, hdt, hdout, hrow.output, hbout]
    rfl
  · unfold RowRequest.sourceClock
    dsimp only [RowRequest.point] at hn2
    omega

end NearQuarticWires.StagePullback
