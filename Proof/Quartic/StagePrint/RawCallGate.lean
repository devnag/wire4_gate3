import Proof.Quartic.StagePrint.RawWidth

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the original public call header supplies the common field width before selection from its first raw occurrence bank. -/
def firstCallGate : St VV := .seq pHead (.seq setOriginalWidth
  (.seq readNat selectOriginalGate))

/-- `lem:print`, paper/paper.tex: the selected original raw occurrence is obtained from the actual public call prefix, with no decoded gate or precomputed child stream as input. -/
theorem firstCallGate_run (C : Ctx) (c : Call) (j : Fin c.first.gates.length)
    (hB : NearCubicGates.Close.Tabulator.GateBits (Call.B0 c.n) c.first.gates[j.val])
    (suffix : List Bool) (a : DS VV) (hc : Cst a)
    (hcw : C.cw.drop a.cp=callWord c++suffix)
    (hj : a.env selectedGate=j.val)
    (hspace : 5*(C.cw.length+2)^2≤C.Wd) :
    Hs C firstCallGate a
      (100*C.cw.length+200+(5*Nat.clog 2 (c.n+1)+30)+
        (30*natBitLength c.first.gates.length+30)+
        selectOriginalCost C j.val (originalChildRequest (Call.B0 c.n) c.first.gates[j.val] hB)+3)
      (fun b=>b.out=a.out++(originalChildRequest (Call.B0 c.n) c.first.gates[j.val] hB).word ∧
        b.wq=a.wq ∧ Cst b) := by
  let r:=originalChildRequest (Call.B0 c.n) c.first.gates[j.val] hB
  have hcall:=len_le_of_drop hcw
  have hflat : (c.first.gates.flatMap gateWord).length≤(callWord c).length := by
    simp only [callWord,circuitWord,listWord,List.length_append]
    omega
  have hn : c.n≤C.cw.length := (gate_fields_le_bank c.first.gates j).2.2.trans (hflat.trans hcall)
  have hclog : Nat.clog 2 (c.n+1)≤C.cw.length+1 := by
    apply Nat.clog_le_of_le_pow
    exact (by omega :c.n+1≤C.cw.length+1).trans Nat.lt_two_pow_self.le
  have hmul : c.n*Nat.clog 2 (c.n+1)≤C.cw.length*(C.cw.length+1) :=
    Nat.mul_le_mul hn hclog
  have hwval : r.W+1≤C.Wd := by
    simp only [r,originalChildRequest,originalFieldWidth,Call.B0]
    nlinarith
  have hwidth : r.W+1<2^C.Wd:=lt_of_le_of_lt hwval Nat.lt_two_pow_self
  have hwidth' : Call.B0 c.n+Nat.clog 2 (c.n+1)+5<2^C.Wd := by
    have hh : r.W+1=Call.B0 c.n+Nat.clog 2 (c.n+1)+5 := by
      change (Call.B0 c.n+Nat.clog 2 (c.n+1)+4)+1=_
      omega
    rw [←hh]
    exact hwidth
  have hmath : 2*(c.n+1)+2<2^C.Wd:=lt_of_le_of_lt (by nlinarith) Nat.lt_two_pow_self
  have hW : 2*C.cw.length+8≤C.Wd:=by nlinarith
  have hL : C.cw.length+2<2^C.Wd:=lt_of_le_of_lt (by nlinarith) Nat.lt_two_pow_self
  have hp : C.cw.drop a.cp=natWord c.n++natWord (kindTag c.kind)++
      (circuitWord c.first++circuitWord c.second++listWord natWord c.parity++ratWord c.radius++suffix) := by
    rw [hcw,callWord]
    simp only [List.append_assoc]
  unfold firstCallGate
  refine Hs.mono (Hs.seq (t1:=100*C.cw.length+200)
    (t2:=(5*Nat.clog 2 (c.n+1)+30)+(30*natBitLength c.first.gates.length+30)+
      selectOriginalCost C j.val r+2)
    (pHead_spec c a hc _ hp hW hL) (fun b ⟨bn,_,bB,bp,bw,bo,bc,bf⟩=>?_))
      (by dsimp only [r];omega) (fun _ h=>h)
  have bd : C.cw.drop b.cp=circuitWord c.first++
      (circuitWord c.second++listWord natWord c.parity++ratWord c.radius++suffix) := by
    rw [bp,←List.drop_drop,←List.drop_drop,hp,List.append_assoc,List.drop_left,List.drop_left]
    simp only [List.append_assoc]
  have bj : b.env selectedGate=j.val := by rw [bf selectedGate (by decide)];exact hj
  refine Hs.mono (Hs.seq (t1:=5*Nat.clog 2 (c.n+1)+30)
    (t2:=(30*natBitLength c.first.gates.length+30)+selectOriginalCost C j.val r+1)
    (setOriginalWidth_run C b bc c.n (Call.B0 c.n) bn bB hmath hwidth')
    (fun e ⟨ewidth,ep,ew,eo,ec,ef⟩=>?_)) (by omega) (fun _ h=>h)
  have ed : C.cw.drop e.cp=natWord c.first.gates.length++
      (c.first.gates.flatMap gateWord++(listWord intWord c.first.coeffs++
        listWord bitWord c.first.table++circuitWord c.second++listWord natWord c.parity++ratWord c.radius++suffix)) := by
    rw [ep,bd,circuitWord,listWord]
    simp only [List.append_assoc]
  have hG : natBitLength c.first.gates.length≤C.cw.length := by
    have hs:=natBitLength_le_len c.first.gates.length
    have hh:=congrArg List.length ed
    simp only [List.length_drop,List.length_append] at hh
    omega
  have ej : e.env selectedGate=j.val := by rw [ef selectedGate (by decide)];exact bj
  refine Hs.seq (t1:=30*natBitLength c.first.gates.length+30)
    (t2:=selectOriginalCost C j.val r)
    (readNat_spec e ec c.first.gates.length _ ed (by omega) hL)
    (fun f ⟨_,_,fp,fw,fo,fc,ff⟩=>?_)
  have fd : C.cw.drop f.cp=c.first.gates.flatMap gateWord++
      (listWord intWord c.first.coeffs++listWord bitWord c.first.table++circuitWord c.second++
        listWord natWord c.parity++ratWord c.radius++suffix) := by
    rw [fp,←List.drop_drop,ed,List.drop_left]
  have fj : f.env selectedGate=j.val := by rw [ff selectedGate (by decide)];exact ej
  have fwidth : f.env width=r.W+1 := by
    rw [ff width (by decide)]
    exact ewidth
  refine (selectOriginalGate_run C (Call.B0 c.n) c.first.gates j hB _ f fc fd
    fwidth fj hwidth (by nlinarith)).mono le_rfl ?_
  rintro g ⟨go,_,gw,gc⟩
  exact ⟨by rw [go,fo,eo,bo],gw.trans (fw.trans (ew.trans bw)),gc⟩

end NearQuarticWires.StagePrint.RawBits
