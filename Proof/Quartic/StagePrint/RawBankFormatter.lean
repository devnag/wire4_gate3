import Proof.Quartic.StagePrint.RawBankSelect
import Proof.Quartic.StagePrint.RawSourceBounds
import Proof.Quartic.StagePrint.OriginalChildBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces (gateWord intWord listWord)
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires

/-- `lem:print`, paper/paper.tex: original-bank selection precedes exact field conversion without duplicating or replacing any raw gate. -/
def selectOriginalGate : St VV := .seq (.op (.zero cWOK))
  (.seq (.op (.zero sourceGateIndex)) (.seq skipOriginalGates formatOriginalGate))

/-- `prop:time`, paper/paper.tex: all preceding original gate words are physically scanned and the selected one is then serialized. -/
def selectOriginalCost (C : Ctx) (j : ℕ) (r : OriginalChildRequest) : ℕ :=
  j*(100*(C.cw.length+2)^2+4)+gateFormatterCost C r+20

/-- `lem:print`, paper/paper.tex: the selected original coefficient and threshold source spans are bounded by the actual raw-bank word. -/
theorem gate_fields_le_bank {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (j : Fin gs.length) :
    (∀z∈List.ofFn gs[j.val].weight,(intWord z).length≤(gs.flatMap gateWord).length) ∧
    (intWord gs[j.val].threshold).length≤(gs.flatMap gateWord).length ∧
    n≤(gs.flatMap gateWord).length := by
  obtain ⟨pre,post,hgs⟩:=List.append_of_mem (List.getElem_mem j.isLt)
  have hg : (gateWord gs[j.val]).length≤(gs.flatMap gateWord).length := by
    conv_rhs=>rw [hgs]
    simp only [List.flatMap_append,List.flatMap_cons,List.length_append]
    omega
  have hh : (gateWord gs[j.val]).length=
      (NearCubicWires.RepairRepresentation.natWord n).length+
      ((List.ofFn gs[j.val].weight).flatMap intWord).length+(intWord gs[j.val].threshold).length := by
    simp [gateWord,listWord,Nat.add_assoc]
  have hc:=dense_count_le_word (List.ofFn gs[j.val].weight)
  simp only [List.length_ofFn] at hc
  refine ⟨?_,by omega,by omega⟩
  intro z hz
  have hzlen:=intWord_member_length (List.ofFn gs[j.val].weight) z hz
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the selected original occurrence is physically located in the complete source bank, then converted to the exact child-compiler input. -/
theorem selectOriginalGate_run (C : Ctx) {n : ℕ} (B : ℕ)
    (gs : List (NormalizedThresholdGate n)) (j : Fin gs.length)
    (hB : NearCubicGates.Close.Tabulator.GateBits B gs[j.val])
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hcw : C.cw.drop a.cp=gs.flatMap gateWord++rest)
    (hw : a.env width=(originalChildRequest B gs[j.val] hB).W+1)
    (hj : a.env selectedGate=j.val)
    (hfield : (originalChildRequest B gs[j.val] hB).W+1<2^C.Wd)
    (hW : C.cw.length+3≤C.Wd) :
    Hs C selectOriginalGate a
      (selectOriginalCost C j.val (originalChildRequest B gs[j.val] hB))
      (fun b=>b.out=a.out++(originalChildRequest B gs[j.val] hB).word ∧
        b.cp=a.cp+((gs.take j.val).flatMap gateWord).length+(gateWord gs[j.val]).length ∧
        b.wq=a.wq ∧ Cst b) := by
  let r:=originalChildRequest B gs[j.val] hB
  obtain ⟨hcfs,hct,hcn⟩:=gate_fields_le_bank gs j
  have hbank : (gs.flatMap gateWord).length≤C.cw.length:=len_le_of_drop hcw
  have hlen : C.cw.length+2<2^C.Wd:=lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  have hctx : 3≤C.Wd:=by omega
  have hcount : (gs.take j.val).length<2^C.Wd := by
    have hh:=length_le_flatMap gs gateWord (fun g=>by
      have hg : 1≤(gateWord g).length := by
        simp [gateWord,listWord,NearCubicGates.Close.Dispatch.natWord_length]
        omega
      exact hg)
    have ht : (gs.take j.val).length≤gs.length := by
      rw [List.length_take];exact min_le_right _ _
    exact lt_of_le_of_lt (ht.trans (hh.trans hbank))
      (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self)
  have hsplit : C.cw.drop a.cp=(gs.take j.val).flatMap gateWord++
      ((gs.drop j.val).flatMap gateWord++rest) := by
    rw [hcw]
    conv_lhs=>rw [←List.take_append_drop j.val gs]
    simp only [List.flatMap_append,List.append_assoc]
  unfold selectOriginalGate
  refine Hx.hs (Hs.then (hs_zero C cWOK a) (fun b hb n1 hn1=>?_))
  subst hb
  refine Hs.then (hs_zero C sourceGateIndex _) (fun e he n2 hn2=>?_)
  subst he
  let e:DS VV:=(a.set cWOK 0).set sourceGateIndex 0
  have ef : Fr a e [cWOK,sourceGateIndex] :=
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))
  have ec : Cst e:=Cst.of_fr hc ef (by decide)
    (by rw [ef vPOS (by decide)];exact hc.pos)
  have ej : e.env selectedGate=(gs.take j.val).length := by
    rw [ef selectedGate (by decide),hj,List.length_take,min_eq_left j.isLt.le]
  refine Hs.then (skipOriginalGates_run C (gs.take j.val) _ e ec
    (by vsimp [e]) (by simp [e]) ej hsplit (by omega) hlen hcount)
    (fun f ⟨fp,fw,fo,_,fc,ff⟩ n3 hn3=>?_)
  have fd : C.cw.drop f.cp=gateWord gs[j.val]++
      ((gs.drop (j.val+1)).flatMap gateWord++rest) := by
    rw [fp]
    change C.cw.drop (a.cp+(List.flatMap gateWord (List.take j.val gs)).length)=_
    rw [←List.drop_drop,hsplit,List.drop_left]
    exact (congrArg (fun xs:List (NormalizedThresholdGate n)=>xs.flatMap gateWord++rest)
      (List.drop_eq_getElem_cons j.isLt)).trans (by simp only [List.flatMap_cons,List.append_assoc])
  have frw : f.env width=r.W+1 := by
    rw [ff width (by decide),ef width (by decide)]
    exact hw
  have fword : C.cw.drop f.cp=listWord intWord r.weights++intWord (r.target+1)++
      ((gs.drop (j.val+1)).flatMap gateWord++rest) := by
    simpa [r,originalChildRequest,gateWord] using fd
  have hcf : ∀z∈r.weights,encS z<2^C.Wd := by
    intro z hz
    have hh:=signed_code_word_bound z C.cw.length ((hcfs z hz).trans hbank)
    have hp:=Nat.pow_le_pow_right (by decide :1≤(2:ℕ)) hW
    omega
  have htf : encS (r.target+1)+3<2^C.Wd := by
    have ht : r.target+1=gs[j.val].threshold:=by simp [r,originalChildRequest]
    rw [ht]
    exact lt_of_lt_of_le (signed_code_word_bound _ _ (hct.trans hbank))
      (Nat.pow_le_pow_right (by decide) hW)
  have hnum : n<2^C.Wd := lt_of_le_of_lt (hcn.trans hbank)
    (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self)
  refine Hs.last (formatOriginalGate_run C f fc r _ fword frw hcf htf hfield
    (by simpa [r,originalChildRequest] using hnum) hctx (by omega) hlen)
    (fun g ⟨go,gp,gw,_,gc,_⟩ n4 hn4=>?_)
  refine ⟨⟨?_,?_,gw.trans fw,gc⟩,?_⟩
  · simpa only [e,DS.set_out] using (show g.out=a.out++r.word by rw [go,fo];rfl)
  · rw [gp,fp]
    have hg : listWord intWord r.weights++intWord (r.target+1)=gateWord gs[j.val] := by
      simp [r,originalChildRequest,gateWord]
    rw [hg]
    rfl
  · unfold selectOriginalCost
    simp only [List.length_take,min_eq_left j.isLt.le] at hn3
    dsimp only [r] at hn4
    omega

end NearQuarticWires.StagePrint.RawBits
