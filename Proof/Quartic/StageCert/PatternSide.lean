import Proof.Quartic.StageCert.PatternDock
import Proof.Quartic.StageCert.PatternPhysical

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `def:mask`, paper/paper.tex: the total numeric source
degree agrees with the actual occurrence-preserving incidence at every
original coordinate. -/
theorem Incidence.sourceDegree_eq (c : Call) (i : Fin c.n) :
    Incidence.sourceDegree c i.val=Cells.incidence (c.first.gates++c.second.gates) i := by
  simp [Incidence.sourceDegree,i.isLt]

/-- `def:mask` and `prop:time`, paper/paper.tex: the complete source-reading side loop returns the exact canonical
structural-mask side bit, in the original pattern order. -/
theorem patternSide_run (C : Ctx) (c : Call) (suffix : List Bool)
    (P : StarParams) (side : Fin (P.r/2)→Fin P.r) (offset cut : ℕ)
    (hside : ∀j,(side j).val=offset+j.val)
    (index : Fin ((P.b+1)^(P.r/2))) (a : DS VV) (hc : Cst a)
    (hb : 1≤P.b)
    (hflag : a.env Incidence.patternFlag=1) (hcut : a.env Incidence.heavyThreshold=cut)
    (hB : a.env Incidence.patternBlockSize=P.b) (hR : a.env Incidence.patternRadix=P.b+1)
    (hstart : a.env Incidence.patternBlock=offset)
    (hend : a.env Incidence.patternEnd=offset+P.r/2)
    (hcode : a.env Incidence.patternCode=index.val) (hsource : P.b*(offset+P.r/2)≤c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd)
    (hradix : 2*(P.b+1)≤2^C.Wd) (hendfit : offset+P.r/2<2^C.Wd) :
    Hs C Incidence.patternLoop a ((P.r/2)*(1204*(C.cw.length+2)^3+2)+2) (fun z =>
      z.env Incidence.patternFlag=
        (patternAvoids P (fun i=>Incidence.sourceDegree c i.val) cut side index).toNat ∧
      z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z Incidence.patternStepScratch) := by
  refine (Incidence.patternLoop_run C c suffix a hc True cut P.b offset index.val (P.r/2)
    hb (by simpa [bnat] using hflag) hcut hB hR hstart hend hcode hsource
    hcw hW hL hn hradix hendfit).mono le_rfl ?_
  rintro z ⟨_,_,zf,zw,zo,zc,zfr⟩
  refine ⟨?_,zw,zo,zc,zfr⟩
  rw [zf,patternAvoids_eq_numeric P c cut offset side hside index]
  simp [bnat,Bool.toNat]

end NearQuarticWires.StageCert
