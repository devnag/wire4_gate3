import Proof.Quartic.StagePullback.PointSetup

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `imp:pullback`, paper/paper.tex: an original
coordinate and complete compact metadata specify one affine flip bit. -/
structure CoordinateRequest where
  point : PointRequest
  coordinate : Fin point.parameters.n

def CoordinateRequest.word (r : CoordinateRequest) : List Bool :=
  r.point.word ++ natWord r.coordinate.val

def CoordinateRequest.answer (r : CoordinateRequest) : Bool := r.point.flip r.coordinate

def CoordinateRequest.output (r : CoordinateRequest) : List Bool := [r.answer]

def firstCoordinate (q : PointRequest) : Fin q.parameters.n :=
  ⟨0, by have := q.parameters.two_le_r; have := q.parameters.four_r_le_n; omega⟩

/-- `imp:pullback`, paper/paper.tex: emit the actual
computed coordinate bit as one ordinary output bit. -/
def emitCoordinateBit : St VV MM :=
  .ite (.eq Flips.accumulator v1) (.op (.emit true)) (.op (.emit false))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the actual binary accumulator determines the written bit. -/
theorem emitCoordinateBit_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (v : Bool) (hv : a.env Flips.accumulator = v.toNat) :
    Hs C emitCoordinateBit a 2 (fun b => b.out = a.out ++ [v]) := by
  unfold emitCoordinateBit
  cases v with
  | false =>
    exact Hs.iteF (by change Flips.accumulator ≠ v1; decide) (by simp [Cnd.eval, hv, hc.one])
      (Hs.mono (hs_emit C false a) le_rfl (by rintro b rfl; rfl))
  | true =>
    exact Hs.iteT (by change Flips.accumulator ≠ v1; decide) (by simp [Cnd.eval, hv, hc.one])
      (Hs.mono (hs_emit C true a) le_rfl (by rintro b rfl; rfl))

/-- `imp:pullback`, paper/paper.tex: one physical
program parses the actual scalar request, decodes its coordinate,
computes its canonical affine flip and emits the resulting bit. -/
def coordinateProgram : St VV MM :=
  .seq pointSetupProgram (.seq (StageGamma.readField MarkerCalls.originalCoordinate)
    (.seq Flips.program emitCoordinateBit))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: original source codes alone physically produce the exact
canonical affine flip bit in polynomially many source operations. -/
theorem coordinateProgram_run (C : Ctx) (a : DS VV MM) (r : CoordinateRequest)
    (hc : Cst a) (hip : a.ip = 0) (hzero : a.env MarkerCalls.originalCoordinate = 0)
    (hinput : C.inp = r.word) (hwidth : r.point.parameters.n + 4 ≤ C.Wd) :
    Hs C coordinateProgram a (600 * (r.point.parameters.n + 2))
      (fun b => b.out = a.out ++ r.output) := by
  have hn : r.point.parameters.n < 2 ^ C.Wd :=
    (Flips.markerWidth C r.point.parameters hwidth).2.2.2
  have hx : natBitLength r.coordinate.val ≤ r.point.parameters.n + 1 := by
    apply NearCubicGates.Close.CounterMachine.CellTablesProg.natBitLength_le_of_lt _ _ (by omega)
    exact r.coordinate.isLt.trans_le
      ((Nat.lt_two_pow_self (n := r.point.parameters.n)).le.trans
        (Nat.pow_le_pow_right (by decide) (by omega)))
  unfold coordinateProgram
  refine Hx.hs (Hs.then (pointSetup_prefix C a r.point (natWord r.coordinate.val)
    (firstCoordinate r.point) hc hip hzero hinput hwidth)
    (fun b ⟨hbi, hbip, hbrest⟩ n1 hn1 => ?_))
  have hin : C.inp.drop b.ip = natWord r.coordinate.val ++ [] := by
    rw [hinput, hbip]
    simp [CoordinateRequest.word]
  refine Hs.then (StageGamma.readField_spec C MarkerCalls.originalCoordinate (by decide)
    (by decide) b hbi.constants r.coordinate.val [] hin (by omega))
    (fun c ⟨hcv, _, hcrest, hcc, hcfr⟩ n2 hn2 => ?_)
  have hci : Flips.Inputs c r.point r.coordinate := ⟨hcc,
    (hcfr _ (by decide)).trans hbi.blocks,
    (hcfr _ (by decide)).trans hbi.translation,
    (hcfr _ (by decide)).trans hbi.left,
    (hcfr _ (by decide)).trans hbi.right,
    (hcfr _ (by decide)).trans hbi.useLeft,
    (hcfr _ (by decide)).trans hbi.useRight,
    (hcfr _ (by decide)).trans hbi.half,
    hcv, (hcfr _ (by decide)).trans hbi.blockWidth,
    (hcfr _ (by decide)).trans hbi.radix⟩
  refine Hs.then (Flips.program_run C c r.point r.coordinate hci hwidth)
    (fun d ⟨hdv, hdsh, hdfr⟩ n3 hn3 => ?_)
  have hdi := hci.frame hdfr
  refine Hs.last (emitCoordinateBit_run C d hdi.constants r.answer hdv) ?_
  rintro e he n4 hn4
  have hdout : d.out = c.out := (Same.of_sh hdsh).out
  have hcout : c.out = b.out := congrArg Prod.fst hcrest
  have hbout : b.out = a.out := congrArg Prod.fst hbrest
  refine ⟨by simpa only [hdout, hcout, hbout, CoordinateRequest.output] using he, ?_⟩
  have hdiv : r.coordinate.val / r.point.parameters.b ≤ r.point.parameters.n :=
    (Nat.div_le_self _ _).trans r.coordinate.isLt.le
  omega

end NearQuarticWires.StagePullback
