import Proof.Quartic.StagePrint.RawCircuitGate

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the complete first circuit is physically consumed before selecting an occurrence in the second raw bank. -/
def secondCallGate : St VV := .seq pHead (.seq parseCirc circuitOriginalGate)

/-- `lem:print` and `prop:time`, paper/paper.tex: selection in the paired target's second bank charges the actual first-circuit scan and retains all original source and threshold semantics. -/
theorem secondCallGate_run (C : Ctx) (c : Call) (j : Fin c.second.gates.length)
    (hB : NearCubicGates.Close.Tabulator.GateBits (Call.B0 c.n) c.second.gates[j.val])
    (suffix : List Bool) (a : DS VV) (hc : Cst a)
    (hcw : C.cw.drop a.cp=callWord c++suffix)
    (hj : a.env selectedGate=j.val) (hspace : 5*(C.cw.length+2)^2≤C.Wd) :
    Hs C secondCallGate a
      ((100*C.cw.length+200)+circCost C.cw.length+
        ((5*Nat.clog 2 (c.n+1)+30)+(30*natBitLength c.second.gates.length+30)+
        selectOriginalCost C j.val (originalChildRequest (Call.B0 c.n) c.second.gates[j.val] hB)+2)+2)
      (fun b=>b.out=a.out++(originalChildRequest (Call.B0 c.n) c.second.gates[j.val] hB).word ∧
        b.wq=a.wq ∧ Cst b) := by
  let r:=originalChildRequest (Call.B0 c.n) c.second.gates[j.val] hB
  have hW : 2*C.cw.length+8≤C.Wd:=by nlinarith
  have hL : C.cw.length+2<2^C.Wd:=lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  have hp : C.cw.drop a.cp=natWord c.n++natWord (kindTag c.kind)++
      (circuitWord c.first++(circuitWord c.second++listWord natWord c.parity++ratWord c.radius++suffix)) := by
    rw [hcw,callWord]
    simp only [List.append_assoc]
  unfold secondCallGate
  refine Hs.mono (Hs.seq (t1:=100*C.cw.length+200)
    (t2:=circCost C.cw.length+
      ((5*Nat.clog 2 (c.n+1)+30)+(30*natBitLength c.second.gates.length+30)+
        selectOriginalCost C j.val r+2)+1)
    (pHead_spec c a hc _ hp hW hL) (fun b ⟨bn,_,bB,bp,bw,bo,bc,bf⟩=>?_))
      (by dsimp only [r];omega) (fun _ h=>h)
  have bd : C.cw.drop b.cp=circuitWord c.first++
      (circuitWord c.second++listWord natWord c.parity++ratWord c.radius++suffix) := by
    rw [bp,←List.drop_drop,←List.drop_drop,hp,List.append_assoc,List.drop_left,List.drop_left]
  have bj : b.env selectedGate=j.val := by rw [bf selectedGate (by decide)];exact hj
  refine Hs.seq (t1:=circCost C.cw.length)
    (t2:=(5*Nat.clog 2 (c.n+1)+30)+(30*natBitLength c.second.gates.length+30)+
      selectOriginalCost C j.val r+2)
    (parseCirc_spec c.first b bc _ bd (by omega) hL)
    (fun e ⟨_,ep,ew,eo,ec,ef⟩=>?_)
  have ed : C.cw.drop e.cp=circuitWord c.second++
      (listWord natWord c.parity++ratWord c.radius++suffix) := by
    rw [ep,←List.drop_drop,bd,List.drop_left]
    simp only [List.append_assoc]
  have en : e.env vN=c.n := by rw [ef vN (by decide)];exact bn
  have eB : e.env vB0=Call.B0 c.n := by rw [ef vB0 (by decide)];exact bB
  have ej : e.env selectedGate=j.val := by rw [ef selectedGate (by decide)];exact bj
  refine (circuitOriginalGate_run C c.second j hB _ e ec ed en eB ej hspace).mono le_rfl ?_
  rintro f ⟨fo,fw,fc⟩
  exact ⟨by rw [fo,eo,bo],fw.trans (ew.trans bw),fc⟩

end NearQuarticWires.StagePrint.RawBits
