import Proof.Quartic.StageMainMask.PointPrefix
import Proof.Quartic.StagePullback.PointRetained

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePullback

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: these are exactly the retained actual scalar
fields used at every original coordinate of one canonical affine point. -/
structure PointData (a : DS VV MM) (q : PointRequest) : Prop where
  constants : Cst a
  fields : ∀ i : Fin 9, a.env (pointFieldRegister i) =
    q.fields[i.val]'(by rw [PointRequest.fields_length]; exact i.isLt)
  useLeft : a.env Flips.leftFlag = q.useLeft.toNat
  useRight : a.env Flips.rightFlag = q.useRight.toNat
  half : a.env Flips.halfCount = q.parameters.r / 2
  blockWidth : a.env Offsets.blockWidth = q.parameters.b
  radix : a.env Digits.radix = 2 ^ q.parameters.s

/-- `imp:pullback`, paper/paper.tex: the scalar
coordinate-bit procedure receives the literal retained point metadata. -/
theorem PointData.inputs {a : DS VV MM} {q : PointRequest} (h : PointData a q)
    (x : Fin q.parameters.n) (hx : a.env MarkerCalls.originalCoordinate = x.val) :
    Flips.Inputs a q x := by
  refine ⟨h.constants, ?_, ?_, ?_, ?_, h.useLeft, h.useRight, h.half, hx,
    h.blockWidth, h.radix⟩
  · simpa [VV, pointFieldRegister, PointRequest.fields] using h.fields 1
  · simpa [VV, pointFieldRegister, PointRequest.fields] using h.fields 4
  · simpa [VV, pointFieldRegister, PointRequest.fields] using h.fields 7
  · simpa [VV, pointFieldRegister, PointRequest.fields] using h.fields 8

/-- `imp:partition`, paper/paper.tex: the actual
original point scalar parser supplies the loop's retained metadata. -/
theorem PointData.of_setup {C : Ctx} (a : DS VV MM) (q : PointRequest)
    (x : Fin q.parameters.n) (hc : Cst a) (hip : a.ip = 0)
    (hcoord : a.env MarkerCalls.originalCoordinate = x.val)
    (rest : List Bool) (hinput : C.inp = q.word ++ rest)
    (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C pointSetupProgram a (400 * (q.parameters.n + 2)) (fun b =>
      PointData b q ∧ b.ip = q.word.length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)) := by
  refine (pointSetup_prefix_fields C a q rest x hc hip hcoord hinput hwidth).mono le_rfl ?_
  rintro b ⟨hbfields, hi, hbip, hbrest⟩
  exact ⟨⟨hi.constants, hbfields, hi.useLeft, hi.useRight, hi.half, hi.blockWidth, hi.radix⟩,
    hbip, hbrest⟩

end NearQuarticWires.StageMainMask
