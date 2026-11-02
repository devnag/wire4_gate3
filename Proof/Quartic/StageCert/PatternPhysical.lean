import Proof.Quartic.StageCert.PatternLoop
import Proof.Gates.Dispatch.Compile

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms

/-- `def:mask` and `prop:time`, paper/paper.tex: the original numeric side pattern is checked by a concrete
multitape program, including every raw-coordinate source scan. -/
theorem patternLoop_physical (C : Ctx) (c : Call) (suffix : List Bool)
    (a : DS VV) (hc : Cst a) (ha : Valid C a) (P : Prop) [Decidable P]
    (cut b offset code count : ℕ) (hb : 1≤b)
    (hflag : a.env patternFlag=bnat P) (hcut : a.env heavyThreshold=cut)
    (hB : a.env patternBlockSize=b) (hR : a.env patternRadix=b+1)
    (hstart : a.env patternBlock=offset) (hend : a.env patternEnd=offset+count)
    (hcode : a.env patternCode=code) (hsource : b*(offset+count)≤c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd)
    (hradix : 2*(b+1)≤2^C.Wd) (hendfit : offset+count<2^C.Wd)
    (inp : List Bool) (p0 cap : ℕ) (hlay : WitLayout inp p0 C.wit)
    (hcapW : 2*C.Wd+1≤cap) (hcapC : C.cw.length+1≤cap)
    (hcapI : p0+4*C.wit.length+4≤cap)
    (hcapO : a.out.length+(count*(1204*(C.cw.length+2)^3+2)+2)≤cap) :
    ∃z,WXExec cap (comp patternLoop) (E C inp p0 a) (E C inp p0 z)
        ((count*(1204*(C.cw.length+2)^3+2)+2)*KC C.Wd) ∧
      z.env patternCode=code/(b+1)^count ∧ z.env patternBlock=offset+count ∧
      z.env patternFlag=bnat (P ∧ prefixNonheavy c cut b offset code count) ∧
      z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z patternStepScratch := by
  obtain ⟨z,t,hex,ht,zc,zb,zf,zw,zo,zconst,zfr⟩ :=
    patternLoop_run C c suffix a hc P cut b offset code count hb hflag hcut hB hR
      hstart hend hcode hsource hcw hW hL hn hradix hendfit
  have hr := (comp_ok C inp p0 cap hlay (by omega) (by omega)
    hcapW hcapC hcapI hex ha (by omega)).1
  exact ⟨z,WXExec.mono hr (Nat.mul_le_mul_right _ ht),zc,zb,zf,zw,zo,zconst,zfr⟩

end NearQuarticWires.StageCert.Incidence
