import Proof.Quartic.StagePrint.RawWidth

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)

/-- `lem:print`, paper/paper.tex: any original circuit occurrence bank is scanned at its actual source position. -/
def circuitOriginalGate : St VV := .seq setOriginalWidth (.seq readNat selectOriginalGate)

/-- `lem:print`, paper/paper.tex: the common original field width fits a quadratic workspace in the source span whenever that span contains an original gate. -/
theorem originalWidth_le_source (n L : ℕ) (hn : n≤L) :
    originalFieldWidth n (Call.B0 n)+1≤5*(L+2)^2 := by
  have hlog : Nat.clog 2 (n+1)≤L+1 := by
    apply Nat.clog_le_of_le_pow
    exact (by omega :n+1≤L+1).trans Nat.lt_two_pow_self.le
  have hmul:=Nat.mul_le_mul hn hlog
  unfold originalFieldWidth Call.B0
  nlinarith

/-- `lem:print` and `prop:time`, paper/paper.tex: a selected original gate is constructed directly from either actual circuit source, with a computed field width and an explicit prefix-scan clock. -/
theorem circuitOriginalGate_run (C : Ctx) {n : ℕ} (Cc : NCircuit n)
    (j : Fin Cc.gates.length)
    (hB : NearCubicGates.Close.Tabulator.GateBits (Call.B0 n) Cc.gates[j.val])
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hcw : C.cw.drop a.cp=circuitWord Cc++rest)
    (hn : a.env vN=n) (hBound : a.env vB0=Call.B0 n)
    (hj : a.env selectedGate=j.val) (hspace : 5*(C.cw.length+2)^2≤C.Wd) :
    Hs C circuitOriginalGate a
      ((5*Nat.clog 2 (n+1)+30)+(30*natBitLength Cc.gates.length+30)+
        selectOriginalCost C j.val (originalChildRequest (Call.B0 n) Cc.gates[j.val] hB)+2)
      (fun b=>b.out=a.out++(originalChildRequest (Call.B0 n) Cc.gates[j.val] hB).word ∧
        b.wq=a.wq ∧ Cst b) := by
  let r:=originalChildRequest (Call.B0 n) Cc.gates[j.val] hB
  have hcwlen:=len_le_of_drop hcw
  have hflat : (Cc.gates.flatMap gateWord).length≤(circuitWord Cc).length := by
    simp only [circuitWord,listWord,List.length_append]
    omega
  have hdim : n≤C.cw.length := (gate_fields_le_bank Cc.gates j).2.2.trans (hflat.trans hcwlen)
  have hW : C.cw.length+3≤C.Wd := by nlinarith
  have hL : C.cw.length+2<2^C.Wd := lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  have hwidth : r.W+1<2^C.Wd := lt_of_le_of_lt
    ((originalWidth_le_source n _ hdim).trans hspace) Nat.lt_two_pow_self
  have hwidth' : Call.B0 n+Nat.clog 2 (n+1)+5<2^C.Wd := by
    have hh : r.W+1=Call.B0 n+Nat.clog 2 (n+1)+5 := by
      change (Call.B0 n+Nat.clog 2 (n+1)+4)+1=_
      omega
    rw [←hh]
    exact hwidth
  have hmath : 2*(n+1)+2<2^C.Wd := lt_of_le_of_lt (by nlinarith) Nat.lt_two_pow_self
  unfold circuitOriginalGate
  refine Hs.mono (Hs.seq (t1:=5*Nat.clog 2 (n+1)+30)
    (t2:=(30*natBitLength Cc.gates.length+30)+selectOriginalCost C j.val r+1)
    (setOriginalWidth_run C a hc n (Call.B0 n) hn hBound hmath hwidth')
    (fun e ⟨ewidth,ep,ew,eo,ec,ef⟩=>?_)) (by dsimp only [r];omega) (fun _ h=>h)
  have ed : C.cw.drop e.cp=natWord Cc.gates.length++
      (Cc.gates.flatMap gateWord++(listWord intWord Cc.coeffs++listWord bitWord Cc.table++rest)) := by
    rw [ep,hcw,circuitWord,listWord]
    simp only [List.append_assoc]
  have hG : natBitLength Cc.gates.length≤C.cw.length := by
    have hs:=natBitLength_le_len Cc.gates.length
    have hh:=congrArg List.length ed
    simp only [List.length_drop,List.length_append] at hh
    omega
  have ej : e.env selectedGate=j.val := by rw [ef selectedGate (by decide)];exact hj
  refine Hs.seq (t1:=30*natBitLength Cc.gates.length+30)
    (t2:=selectOriginalCost C j.val r)
    (readNat_spec e ec Cc.gates.length _ ed (by omega) hL)
    (fun f ⟨_,_,fp,fw,fo,fc,ff⟩=>?_)
  have fd : C.cw.drop f.cp=Cc.gates.flatMap gateWord++
      (listWord intWord Cc.coeffs++listWord bitWord Cc.table++rest) := by
    rw [fp,←List.drop_drop,ed,List.drop_left]
  have fj : f.env selectedGate=j.val := by rw [ff selectedGate (by decide)];exact ej
  have fwidth : f.env width=r.W+1 := by rw [ff width (by decide)];exact ewidth
  refine (selectOriginalGate_run C (Call.B0 n) Cc.gates j hB _ f fc fd
    fwidth fj hwidth hW).mono le_rfl ?_
  rintro g ⟨go,_,gw,gc⟩
  exact ⟨by rw [go,fo,eo],gw.trans (fw.trans ew),gc⟩

end NearQuarticWires.StagePrint.RawBits
