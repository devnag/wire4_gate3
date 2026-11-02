import Proof.Quartic.StageCert.IncidenceLists
import Proof.Quartic.Cells.Score

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `sec:cells`, paper/paper.tex: the numeric raw-coordinate
census is exactly the paper's occurrence-preserving incidence. -/
theorem coordinateSum_eq_incidence {n : ℕ} (gs : List (NormalizedThresholdGate n)) (i : Fin n) :
    coordinateSum gs i=Cells.incidence gs i := by
  unfold coordinateSum Cells.incidence
  congr 1
  apply List.map_congr_left
  intro g _
  by_cases h : g.weight i=0 <;> simp [wireBit,h]

/-- `sec:cells`, paper/paper.tex: a circuit incidence scan
reads the original occurrences, then consumes all coefficient and table fields. -/
def readCoordinateCircuit : St VV := .seq readCoordinateGateList (.seq pc2 pc3)

/-- `sec:cells`, paper/paper.tex: the circuit scan preserves
all original-coordinate and caller state outside this explicit frame. -/
def circuitScratch : List (Fin VV) := gateListScratch++pc2T++pc3T

/-- `sec:cells` and `prop:time`, paper/paper.tex: exact coordinate incidence is physically extracted from the
complete original circuit word in polynomial binary time. -/
theorem readCoordinateCircuit_run (C : Ctx) {n : ℕ} (Cc : NCircuit n) (i : Fin n)
    (rest : List Bool) (a : DS VV) (hc : Cst a) (hcoord : a.env coordinate=i.val)
    (hin : C.cw.drop a.cp=circuitWord Cc++rest)
    (hW : 2*C.cw.length+2≤C.Wd) (hL : C.cw.length+2<2^C.Wd)
    (ht : a.env censusTotal+(circuitWord Cc).length+2<2^C.Wd) :
    Hs C readCoordinateCircuit a (500*(C.cw.length+2)^3) (fun b =>
      b.env censusTotal=a.env censusTotal+Cells.incidence Cc.gates i ∧
      b.cp=a.cp+(circuitWord Cc).length ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      Fr a b circuitScratch) := by
  have hclen : (Cc.gates.flatMap gateWord).length≤(circuitWord Cc).length := by
    simp only [circuitWord,listWord,List.length_append]
    omega
  simp only [circuitWord,List.append_assoc] at hin
  unfold readCoordinateCircuit
  refine Hx.hs (Hs.then (readCoordinateGateList_run C Cc.gates i
    (listWord intWord Cc.coeffs++listWord bitWord Cc.table++rest) a hc hcoord
    (by simpa only [List.append_assoc] using hin) (by omega) hL (by omega))
    (fun b ⟨bt,bc,bw,bo,bconst,bf⟩ n1 hn1 => ?_))
  have bword : C.cw.drop b.cp=listWord intWord Cc.coeffs++(listWord bitWord Cc.table++rest) := by
    rw [bc,←List.drop_drop,hin,List.drop_left]
  refine Hs.then (pc2_spec Cc.coeffs b bconst _ bword hW hL)
    (fun d ⟨_nz,_sum,_len,_pos,dc,dw,doo,dconst,df⟩ n2 hn2 => ?_)
  have dword : C.cw.drop d.cp=listWord bitWord Cc.table++rest := by
    rw [dc,←List.drop_drop,bword,List.drop_left]
  refine Hs.last (pc3_spec Cc.table d dconst _ dword hW hL)
    (fun e ⟨_bit,_len,ec,ew,eo,econst,ef⟩ n3 hn3 => ?_)
  refine ⟨⟨?_,?_,ew.trans (dw.trans bw),eo.trans (doo.trans bo),econst,
    (bf.weaken (by simp only [circuitScratch,List.mem_append]; tauto)).trans
      ((df.weaken (by simp only [circuitScratch,List.mem_append]; tauto)).trans
        (ef.weaken (by simp only [circuitScratch,List.mem_append]; tauto)))⟩,?_⟩
  · rw [ef censusTotal (by decide),df censusTotal (by decide),bt,coordinateSum_eq_incidence]
  · rw [ec,dc,bc]
    simp only [circuitWord,List.length_append]
    omega
  · have hp : (C.cw.length+2)^2≤(C.cw.length+2)^3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 1≤(C.cw.length+2)^3 := Nat.pow_pos (by omega)
    have hgap : 2*(C.cw.length+2)^2≤(C.cw.length+2)^3 := by nlinarith
    nlinarith only [hn1,hn2,hn3,hgap,hpos]

end NearQuarticWires.StageCert.Incidence
