import Proof.Quartic.StageCert.PatternStart
import Proof.Quartic.StageCert.PatternSide

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-- `def:mask`, paper/paper.tex: side initialization and
the exact finite original-coordinate scan form one arithmetic program. -/
def Incidence.patternSideProgram : St VV := .seq Incidence.startPattern Incidence.patternLoop

/-- `def:mask`, paper/paper.tex: the endpoint register is
the only additional scratch register needed by side initialization. -/
def Incidence.patternSideScratch : List (Fin VV) := Incidence.patternEnd::Incidence.patternStepScratch

/-- `def:mask` and `prop:time`, paper/paper.tex: a canonical numeric error pattern is converted to its exact
structural side bit by one complete physical arithmetic program. -/
theorem patternSideProgram_run (C : Ctx) (c : Call) (suffix : List Bool)
    (P : StarParams) (side : Fin (P.r/2)→Fin P.r) (offset cut : ℕ)
    (hside : ∀j,(side j).val=offset+j.val)
    (index : Fin ((P.b+1)^(P.r/2))) (a : DS VV) (hc : Cst a)
    (hb : 1≤P.b) (hcut : a.env Incidence.heavyThreshold=cut)
    (hB : a.env Incidence.patternBlockSize=P.b) (hR : a.env Incidence.patternRadix=P.b+1)
    (hoff : a.env Incidence.patternOffset=offset)
    (hcount : a.env Incidence.patternCount=P.r/2)
    (hinput : a.env Incidence.patternInput=index.val) (hsource : P.b*(offset+P.r/2)≤c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd)
    (hradix : 2*(P.b+1)≤2^C.Wd) (hendfit : offset+P.r/2<2^C.Wd) :
    Hs C Incidence.patternSideProgram a
      ((P.r/2)*(1204*(C.cw.length+2)^3+2)+12) (fun z =>
      z.env Incidence.patternFlag=
        (patternAvoids P (fun i=>Incidence.sourceDegree c i.val) cut side index).toNat ∧
      z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z Incidence.patternSideScratch) := by
  unfold Incidence.patternSideProgram
  refine (Hs.seq (t1 := 9) (t2 := (P.r/2)*(1204*(C.cw.length+2)^3+2)+2)
    (Incidence.startPattern_run C a hc (by rw [hoff,hcount]; exact hendfit)) ?_).mono
      (by omega) (fun _ h => h)
  rintro z ⟨zb,ze,zc,zf,_zcp,zw,zo,zconst,zfr⟩
  refine (patternSide_run C c suffix P side offset cut hside index z zconst hb zf
    ((zfr _ (by decide)).trans hcut) ((zfr _ (by decide)).trans hB)
    ((zfr _ (by decide)).trans hR) (zb.trans hoff)
    (by simpa only [hoff,hcount] using ze) (zc.trans hinput) hsource
    hcw hW hL hn hradix hendfit).mono le_rfl ?_
  rintro d ⟨df,dw,doo,dconst,dfr⟩
  refine ⟨df,dw.trans zw,doo.trans zo,dconst,?_⟩
  exact (zfr.weaken (by
      simp only [Incidence.patternStartScratch,Incidence.patternSideScratch,
        Incidence.patternStepScratch,Incidence.patternVisitScratch,List.mem_cons,List.mem_append,
        List.not_mem_nil,or_false]
      tauto)).trans (dfr.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))

end NearQuarticWires.StageCert
