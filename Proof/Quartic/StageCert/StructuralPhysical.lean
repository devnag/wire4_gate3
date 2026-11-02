import Proof.Quartic.StageCert.StructuralProgram
import Proof.Gates.Dispatch.Compile

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open Incidence

/-- `def:mask` and `prop:time`, paper/paper.tex: the complete exact original-source structural-mask procedure
is realized by one physical multitape program with explicit capacities. -/
theorem structuralProgram_physical (C : Ctx) (c : Call) (suffix : List Bool)
    (P : StarParams) (cut : ℕ) (u v : Fin ((P.b+1)^(P.r/2)))
    (a : DS VV) (hc : Cst a) (ha : Valid C a) (hb : 1≤P.b)
    (hcut : a.env heavyThreshold=cut) (hB : a.env patternBlockSize=P.b)
    (hR : a.env patternRadix=P.b+1) (hcount : a.env patternCount=P.r/2)
    (hu : a.env patternLeftInput=u.val) (hv : a.env patternRightInput=v.val)
    (hsource : P.b*P.r≤c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd)
    (hradix : 2*(P.b+1)≤2^C.Wd) (hrfit : P.r<2^C.Wd)
    (inp : List Bool) (p0 cap : ℕ) (hlay : WitLayout inp p0 C.wit)
    (hcapW : 2*C.Wd+1≤cap) (hcapC : C.cw.length+1≤cap)
    (hcapI : p0+4*C.wit.length+4≤cap)
    (hcapO : a.out.length+(2*(P.r/2)*(1204*(C.cw.length+2)^3+2)+40)≤cap) :
    ∃z,WXExec cap (comp structuralProgram) (E C inp p0 a) (E C inp p0 z)
        ((2*(P.r/2)*(1204*(C.cw.length+2)^3+2)+40)*KC C.Wd) ∧
      z.env patternFlag=(Mask.structuralMask (P.flipSet P.leftBlock) (P.flipSet P.rightBlock)
        (Mask.heavyCoordinates (fun i=>sourceDegree c i.val) cut)
        ((errorsEquiv P).symm u) ((errorsEquiv P).symm v)).toNat ∧
      z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z structuralScratch := by
  obtain ⟨z,t,hex,ht,zf,zw,zo,zconst,zfr⟩ :=
    structuralProgram_run C c suffix P cut u v a hc hb hcut hB hR hcount hu hv
      hsource hcw hW hL hn hradix hrfit
  have hr := (comp_ok C inp p0 cap hlay (by omega) (by omega)
    hcapW hcapC hcapI hex ha (by omega)).1
  exact ⟨z,WXExec.mono hr (Nat.mul_le_mul_right _ ht),zf,zw,zo,zconst,zfr⟩

end NearQuarticWires.StageCert
