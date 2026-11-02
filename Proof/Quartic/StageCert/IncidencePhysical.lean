import Proof.Quartic.StageCert.IncidenceStream
import Proof.Gates.Dispatch.Compile

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: original coordinate incidences and heavy flags are computed by
one explicit physical multitape program on the retained raw source word. -/
theorem incidenceStream_physical (C : Ctx) (c : Call) (suffix : List Bool)
    (a : DS VV) (hc : Cst a) (ha : Valid C a)
    (hi : a.env coordinate=0) (hn : a.env arity=c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hfit : c.n<2^C.Wd)
    (inp : List Bool) (p0 cap : ℕ) (hlay : WitLayout inp p0 C.wit)
    (hcapW : 2*C.Wd+1≤cap) (hcapC : C.cw.length+1≤cap)
    (hcapI : p0+4*C.wit.length+4≤cap)
    (hcapO : a.out.length+(c.n*(2000*(C.cw.length+2)^3+2)+2)≤cap) :
    ∃b,WXExec cap (comp incidenceStream) (E C inp p0 a) (E C inp p0 b)
        ((c.n*(2000*(C.cw.length+2)^3+2)+2)*KC C.Wd) ∧
      b.out=a.out++incidencePrefix c (a.env heavyThreshold) c.n ∧
      b.env coordinate=c.n ∧ b.env arity=c.n ∧ b.env heavyThreshold=a.env heavyThreshold ∧
      b.wq=a.wq ∧ Cst b ∧ Fr a b stepScratch := by
  obtain ⟨b,n,hex,hnCost,ho,hi',hn',hh',hw,hc',hf⟩ :=
    incidenceStream_run C c suffix a hc hi hn hcw hW hL hfit
  have hr := (comp_ok C inp p0 cap hlay (by omega) (by omega)
    hcapW hcapC hcapI hex ha (by omega)).1
  exact ⟨b,WXExec.mono hr (Nat.mul_le_mul_right _ hnCost),ho,hi',hn',hh',hw,hc',hf⟩

end NearQuarticWires.StageCert.Incidence
