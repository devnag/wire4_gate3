import Proof.Quartic.StageCert.IncidenceCall

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the original-call incidence scan works at its actual offset in
a larger source record, retaining its exact cursor and witness frame. -/
theorem readCoordinateCall_at_run (C : Ctx) (c : Call) (i : Fin c.n) (suffix : List Bool) (a : DS VV)
    (hc : Cst a) (ht : a.env censusTotal=0)
    (hcoord : a.env coordinate=i.val) (hin : C.cw.drop a.cp=callWord c++suffix)
    (hW : 2*C.cw.length+8≤C.Wd) (hL : 2*C.cw.length+4<2^C.Wd) :
    Hs C readCoordinateCall a (1200*(C.cw.length+2)^3) (fun b =>
      b.env censusTotal=Cells.incidence (c.first.gates++c.second.gates) i ∧
      b.cp=a.cp+pos3 c ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b callScratch) := by
  have hsource : (callWord c).length≤C.cw.length := len_le_of_drop hin
  have hword := congrArg List.length (callWord_eq c)
  simp only [List.length_append] at hword
  have hfirst : (circuitWord c.first).length≤C.cw.length := by omega
  have hboth : (circuitWord c.first).length+(circuitWord c.second).length≤C.cw.length := by
    omega
  have hstart : C.cw.drop a.cp=natWord c.n++natWord (kindTag c.kind)++
      (circuitWord c.first++(circuitWord c.second++(listWord natWord c.parity++ratWord c.radius++suffix))) := by
    rw [hin,callWord_eq]
    simp only [List.append_assoc]
  unfold readCoordinateCall
  refine Hx.hs (Hs.then (pHead_spec c a hc _ hstart hW (by omega))
    (fun b ⟨_n,_kind,_B,bcp,bw,bo,bconst,bf⟩ n1 hn1 => ?_))
  have bpos : b.cp=a.cp+pos1 c := by simp only [bcp,pos1,Nat.add_assoc]
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
    simp only [pos3,pos2,Nat.add_assoc]
  · have hp : C.cw.length+2≤(C.cw.length+2)^3 := Nat.le_self_pow (by norm_num) _
    omega


end NearQuarticWires.StageCert.Incidence
