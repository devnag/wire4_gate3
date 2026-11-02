import Proof.Quartic.StagePrintContext.DoubleFields
import Proof.Quartic.StagePrintContext.EmitCost
import Proof.Quartic.StagePrint.BaseHeaderEmit

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePrint.Header

/-- `lem:print`, paper/paper.tex: compute the
actual original affine header once, then emit its two context frame layers. -/
def emitHeaderField : St VV MM :=
  .seq baseHeaderProgram (doubleFramedFields baseHeaderRegisters)

/-- `prop:time`, paper/paper.tex: every original
source read, geometry operation and new header marker is charged. -/
def headerFieldCost (r : HeaderCall) (width : ℕ) : ℕ :=
  baseHeaderCost r.call r.parameters r.witness+9*fieldClock 7 width+9

/-- `lem:print` and `prop:time`, paper/paper.tex: actual original source and witness produce the literal
header field, retaining the loaded geometry needed by the final field. -/
theorem emitHeaderField_run (C : Ctx) (r : HeaderCall) (a : DS VV MM)
    (hc : Cst a) (ha : Valid C a) (hd : HeaderSourceData r a)
    (hWd : r.call.n+3≤C.Wd) (hcap : 4*(r.call.n+1)^2+r.call.n+20<2^C.Wd) :
    Hs C emitHeaderField a (headerFieldCost r C.Wd) (fun z=>
      z.out=a.out++frame (frame ((baseHeaderValues r).flatMap NearCubicWires.RepairRepresentation.natWord)) ∧
      BaseHeaderData r z ∧z.ram=a.ram ∧z.ip=a.ip ∧
      (z.kin,z.kout,z.kc)=(a.kin,a.kout,a.kc) ∧Cst z ∧Valid C z) := by
  unfold emitHeaderField
  refine (Hs.seq (t2:=9*fieldClock 7 C.Wd+8)
    (baseHeaderProgram_run C r a hc ha hd hWd hcap) ?_).mono
    (by unfold headerFieldCost;omega) (fun _ h=>h)
  rintro b ⟨bh,br,bi,bo,bs,bc,bv⟩
  have er:=doubleFramedFields_run C baseHeaderRegisters b bc bv (by omega) (by decide)
  have heCost:=headerEmitCost_valid C baseHeaderRegisters b bv (by omega)
  change headerEmitCost (baseHeaderRegisters.map b.env)≤fieldClock 7 C.Wd at heCost
  rw [bh.values] at er heCost
  refine er.mono (by omega) ?_
  rintro z ⟨zo,zi,zr,_zrc,zs,zc,zv,zfr⟩
  refine ⟨by rw [zo,bo],?_,zr.trans br,zi.trans bi,zs.trans bs,zc,zv⟩
  constructor
  · rw [zfr arity (by decide)];exact bh.n
  · rw [zfr Lin (by decide)];exact bh.sourceWidth
  · rw [zfr Lout (by decide)];exact bh.targetWidth
  · rw [zfr blockCount (by decide)];exact bh.r
  · rw [zfr blockWidth (by decide)];exact bh.b
  · rw [zfr syndromeWidth (by decide)];exact bh.s
  · rw [zfr translation (by decide)];exact bh.translation

end NearQuarticWires.StagePrintContext
