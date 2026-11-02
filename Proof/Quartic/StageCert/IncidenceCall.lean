import Proof.Quartic.StageCert.IncidenceCircuit
import Proof.Quartic.StagePrep.CensusCall

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:algorithm`, paper/paper.tex: one original-coordinate
scan reads both complete raw banks from the public call word. -/
def readCoordinateCall : St VV :=
  .seq pHead (.seq readCoordinateCircuit readCoordinateCircuit)

/-- `sec:algorithm`, paper/paper.tex: the public header and
circuit-parser scratch frame exclude the selected original coordinate. -/
def callScratch : List (Fin VV) := headT++circuitScratch

/-- `sec:cells`, paper/paper.tex: incidence is additive over
the two occurrence lists, without deduplicating either raw bank. -/
theorem incidence_append {n : ℕ} (xs ys : List (NormalizedThresholdGate n)) (i : Fin n) :
    Cells.incidence (xs++ys) i=Cells.incidence xs i+Cells.incidence ys i := by
  simp [Cells.incidence]

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the physical original-call scan computes the exact combined
coordinate incidence and preserves all witness bits and output bytes. -/
theorem readCoordinateCall_prefix_run (C : Ctx) (c : Call) (i : Fin c.n) (suffix : List Bool) (a : DS VV)
    (hc : Cst a) (hcp : a.cp=0) (ht : a.env censusTotal=0)
    (hcoord : a.env coordinate=i.val) (hcw : C.cw=callWord c++suffix)
    (hW : 2*C.cw.length+8≤C.Wd) (hL : 2*C.cw.length+4<2^C.Wd) :
    Hs C readCoordinateCall a (1200*(C.cw.length+2)^3) (fun b =>
      b.env censusTotal=Cells.incidence (c.first.gates++c.second.gates) i ∧
      b.cp=pos3 c ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b callScratch) := by
  have hword := congrArg List.length (callWord_eq c)
  simp only [List.length_append] at hword
  have hfirst : (circuitWord c.first).length≤C.cw.length := by rw [hcw,List.length_append]; omega
  have hboth : (circuitWord c.first).length+(circuitWord c.second).length≤C.cw.length := by
    rw [hcw,List.length_append]
    omega
  have hstart : C.cw.drop a.cp=natWord c.n++natWord (kindTag c.kind)++
      (circuitWord c.first++(circuitWord c.second++(listWord natWord c.parity++ratWord c.radius++suffix))) := by
    rw [hcp,List.drop_zero,hcw,callWord_eq]
    simp only [List.append_assoc]
  unfold readCoordinateCall
  refine Hx.hs (Hs.then (pHead_spec c a hc _ hstart hW (by omega))
    (fun b ⟨_n,_kind,_B,bcp,bw,bo,bconst,bf⟩ n1 hn1 => ?_))
  have bpos : b.cp=pos1 c := by simp only [bcp,hcp,Nat.zero_add,pos1]
  have bword : C.cw.drop b.cp=circuitWord c.first++
      (circuitWord c.second++(listWord natWord c.parity++ratWord c.radius++suffix)) := by
    rw [bcp]
    have hd := drop_adv (by simpa only [List.append_assoc] using hstart :
      C.cw.drop a.cp=(natWord c.n++natWord (kindTag c.kind))++_)
    simpa only [List.length_append,Nat.add_assoc,List.append_assoc] using hd
  have bt : b.env censusTotal=0 := (bf _ (by decide)).trans ht
  have bi : b.env coordinate=i.val := (bf _ (by decide)).trans hcoord
  refine Hs.then (readCoordinateCircuit_run C c.first i _ b bconst bi bword
    (by omega) (by omega) (by rw [bt]; omega))
    (fun d ⟨dt,dc,dw,doo,dconst,df⟩ n2 hn2 => ?_)
  have dword : C.cw.drop d.cp=circuitWord c.second++(listWord natWord c.parity++ratWord c.radius++suffix) := by
    rw [dc,←List.drop_drop,bword,List.drop_left]
  have dt' : d.env censusTotal=Cells.incidence c.first.gates i := by simpa only [bt,Nat.zero_add] using dt
  have di : d.env coordinate=i.val := (df _ (by decide)).trans bi
  have hprice : Cells.incidence c.first.gates i≤(circuitWord c.first).length := by
    rw [←coordinateSum_eq_incidence]
    exact (coordinateSum_le_charge c.first.gates i).trans (wires_le_circuitWord c.first)
  refine Hs.last (readCoordinateCircuit_run C c.second i _ d dconst di dword
    (by omega) (by omega) (by rw [dt']; omega))
    (fun e ⟨et,ec,ew,eo,econst,ef⟩ n3 hn3 => ?_)
  refine ⟨⟨?_,?_,ew.trans (dw.trans bw),eo.trans (doo.trans bo),econst,
    (bf.weaken (by simp only [callScratch,List.mem_append]; tauto)).trans
      ((df.weaken (by simp only [callScratch,List.mem_append]; tauto)).trans
        (ef.weaken (by simp only [callScratch,List.mem_append]; tauto)))⟩,?_⟩
  · rw [et,dt',incidence_append]
  · rw [ec,dc,bpos]
    rfl
  · have hp : C.cw.length+2≤(C.cw.length+2)^3 := Nat.le_self_pow (by norm_num) _
    omega

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the source-prefix scanner specializes to the original public
call with the same exact incidence, witness frame and physical cost. -/
theorem readCoordinateCall_run (C : Ctx) (c : Call) (i : Fin c.n) (a : DS VV)
    (hc : Cst a) (hcp : a.cp=0) (ht : a.env censusTotal=0)
    (hcoord : a.env coordinate=i.val) (hcw : C.cw=callWord c)
    (hW : 2*C.cw.length+8≤C.Wd) (hL : 2*C.cw.length+4<2^C.Wd) :
    Hs C readCoordinateCall a (1200*(C.cw.length+2)^3) (fun b =>
      b.env censusTotal=Cells.incidence (c.first.gates++c.second.gates) i ∧
      b.cp=pos3 c ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b callScratch) := by
  exact readCoordinateCall_prefix_run C c i [] a hc hcp ht hcoord
    (by simpa only [List.append_nil] using hcw) hW hL

end NearQuarticWires.StageCert.Incidence
