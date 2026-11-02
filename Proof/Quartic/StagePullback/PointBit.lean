import Proof.Quartic.StagePullback.CoordinateFlip
import Proof.Quartic.StageHamming.CenterBit

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: the actual canonical center encoder is followed
by the actual original-coordinate affine translation and error bits. -/
def pointBitProgram : St VV MM :=
  .seq StageHamming.centerBit (.seq Flips.program
    (xorInto Flips.accumulator StageHamming.centerOutput))

def pointBitScratch : List (Fin VV) := StageHamming.centerScratch ++ Flips.scratch

/-- `imp:pullback` and `prop:time`, paper/paper.tex: literal scalar metadata compute one actual original point
bit, without a decoded center or supplied coordinate-bit function. -/
theorem pointBitProgram_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (x : Fin q.parameters.n) (hi : Flips.Inputs a q x)
    (hn : a.env 20 = q.parameters.n) (hr : a.env 21 = q.parameters.r)
    (hb : a.env 22 = q.parameters.b) (hs : a.env 23 = q.parameters.s)
    (hrow : a.env 25 = q.row.val) (hcolumn : a.env 26 = q.column.val)
    (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C pointBitProgram a
      (300 * (q.parameters.n + 1) ^ 3 + 21 * (x.val / q.parameters.b) + 125) (fun b =>
        b.env Flips.accumulator = (q.point x).toNat ∧
        b.sh = a.sh ∧ Fr a b pointBitScratch) := by
  unfold pointBitProgram
  refine Hx.hs (Hs.then (StageHamming.centerBit_spec a hi.constants q.parameters
    q.row.val q.column.val x.val hn hr hb hs hrow hcolumn hi.coordinate x.isLt hwidth)
    (fun b ⟨hbvalue, hbsh, hbfr⟩ n1 hn1 => ?_))
  have hbc : Cst b := hi.constants.of_fr hbfr (by decide)
  have hbi : Flips.Inputs b q x := ⟨hbc,
    (hbfr _ (by decide)).trans hi.blocks,
    (hbfr _ (by decide)).trans hi.translation,
    (hbfr _ (by decide)).trans hi.left,
    (hbfr _ (by decide)).trans hi.right,
    (hbfr _ (by decide)).trans hi.useLeft,
    (hbfr _ (by decide)).trans hi.useRight,
    (hbfr _ (by decide)).trans hi.half,
    (hbfr _ (by decide)).trans hi.coordinate,
    (hbfr _ (by decide)).trans hi.blockWidth,
    (hbfr _ (by decide)).trans hi.radix⟩
  refine Hs.then (Flips.program_run C b q x hbi hwidth)
    (fun c ⟨hcvalue, hcsh, hcfr⟩ n2 hn2 => ?_)
  have hci := hbi.frame hcfr
  have hcenter : c.env StageHamming.centerOutput =
      (PrimT.C4Geo.ctrBit q.parameters q.row.val q.column.val x.val).toNat :=
    (hcfr _ (by decide)).trans hbvalue
  refine Hs.last (xorInto_run C Flips.accumulator StageHamming.centerOutput
    (by decide) (by decide) (by decide) c hci.constants (q.flip x)
    (PrimT.C4Geo.ctrBit q.parameters q.row.val q.column.val x.val) hcvalue hcenter) ?_
  rintro d ⟨hdvalue, hdsh, hdfr⟩ n3 hn3
  have hfb : Fr a b pointBitScratch := hbfr.weaken (by
    intro y hy; exact List.mem_append_left _ hy)
  have hfc : Fr b c pointBitScratch := hcfr.weaken (by
    intro y hy; exact List.mem_append_right _ hy)
  have hfd : Fr c d pointBitScratch := hdfr.weaken (by
    intro y hy
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> decide)
  refine ⟨⟨?_, hdsh.trans (hcsh.trans hbsh), hfb.trans (hfc.trans hfd)⟩, by omega⟩
  simpa only [PointRequest.point_scalar, Bool.xor_comm] using hdvalue

end NearQuarticWires.StagePullback
