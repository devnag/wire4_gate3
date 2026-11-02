import Proof.Quartic.StagePrep.CensusWeights

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Dispatch
open NearQuarticWires.StagePrep

/-- `sec:cells`, paper/paper.tex: the original coordinate
whose raw occurrence incidence is being extracted. -/
def coordinate : Fin VV := ⟨95,by decide⟩

/-- `sec:cells`, paper/paper.tex: one original signed weight
is read in every branch; only the selected coordinate changes the count. -/
def readCoordinateWeight : St VV :=
  .ite (.eq weightIndex coordinate) countWeight readInt

/-- `sec:cells`, paper/paper.tex: the signed original-weight
reader counts exactly the selected nonzero coordinate. -/
theorem readCoordinateWeight_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (z : ℤ) (rest : List Bool)
    (hin : C.cw.drop a.cp=intWord z++rest)
    (hW : C.cw.length+2≤C.Wd) (hL : C.cw.length+2<2^C.Wd)
    (ht : a.env censusTotal+1<2^C.Wd) :
    Hs C readCoordinateWeight a (60*(intWord z).length+74) (fun b =>
      b.env censusTotal=a.env censusTotal+
        (if a.env weightIndex=a.env coordinate then wireBit z else 0) ∧
      b.cp=a.cp+(intWord z).length ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      Fr a b (censusTotal::readIntT)) := by
  unfold readCoordinateWeight
  refine Hs.ite (c := .eq weightIndex coordinate) (show weightIndex≠coordinate by decide) ?_ ?_
  · intro he
    have hsame : a.env weightIndex=a.env coordinate := by
      simpa only [Cnd.eval,decide_eq_true_eq] using he
    exact (countWeight_spec C a hc z rest hin hW hL ht).mono le_rfl
      (fun b hb => by simpa only [if_pos hsame] using hb)
  · intro he
    have hdiff : a.env weightIndex≠a.env coordinate := by
      simpa only [Cnd.eval,decide_eq_false_iff_not] using he
    refine (readInt_spec a hc z rest hin hW hL).mono (by omega) ?_
    rintro b ⟨_hs,_hm,_hh,hcp,hw,ho,hc',hf⟩
    exact ⟨by rw [hf censusTotal (by decide),if_neg hdiff,Nat.add_zero],
      hcp,hw,ho,hc',hf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy)⟩

/-- `sec:cells`, paper/paper.tex: partial scanning changes
one coordinate's incidence by at most one per raw gate. -/
def coordinatePrefix (ws : List ℤ) (coord k : ℕ) : ℕ :=
  if coord<k then wireBit (ws.getD coord 0) else 0

/-- `sec:cells`, paper/paper.tex: the exact partial-incidence
count is a Boolean integer, for every signed weight vector. -/
theorem coordinatePrefix_le_one (ws : List ℤ) (coord k : ℕ) :
    coordinatePrefix ws coord k≤1 := by
  unfold coordinatePrefix wireBit
  split_ifs <;> omega

/-- `sec:cells`, paper/paper.tex: scanning the next original
weight adds exactly its selected-coordinate incidence. -/
theorem coordinatePrefix_step (ws : List ℤ) (coord k : ℕ) (hk : k<ws.length) :
    coordinatePrefix ws coord (k+1)=coordinatePrefix ws coord k+
      (if k=coord then wireBit ws[k] else 0) := by
  by_cases he : k=coord
  · subst coord
    simp only [coordinatePrefix,Nat.lt_succ_self,lt_self_iff_false,if_true,if_false,zero_add]
    rw [List.getD_eq_getElem ws 0 hk]
  · have hlt : coord<k+1↔coord<k := by omega
    simp [coordinatePrefix,hlt,he]

/-- `sec:cells`, paper/paper.tex: the entire original
weight vector is scanned, retaining all signs, zero weights and positions. -/
def readCoordinateWeights : St VV :=
  .loop (.lt weightIndex weightLength) (.seq readCoordinateWeight (.op (.inc weightIndex)))

/-- `sec:cells` and `prop:time`, paper/paper.tex: the physical coordinate census reads the actual dense signed
weights once and produces their exact incidence contribution. -/
theorem readCoordinateWeights_run (C : Ctx) (ws : List ℤ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (coord : ℕ)
    (hcoord : a.env coordinate=coord) (hi : a.env weightIndex=0)
    (hn : a.env weightLength=ws.length)
    (hin : C.cw.drop a.cp=ws.flatMap intWord++rest)
    (hW : C.cw.length+2≤C.Wd) (hL : C.cw.length+2<2^C.Wd)
    (ht : a.env censusTotal+ws.length+1<2^C.Wd) :
    Hs C readCoordinateWeights a (ws.length*(60*C.cw.length+78)+2) (fun b =>
      b.env censusTotal=a.env censusTotal+coordinatePrefix ws coord ws.length ∧
      b.cp=a.cp+(ws.flatMap intWord).length ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      Fr a b (weightIndex::censusTotal::readIntT) ∧
      b.env weightIndex=ws.length ∧ b.env weightLength=ws.length) := by
  let T := weightIndex::censusTotal::readIntT
  let P : ℕ→DS VV→Prop := fun k b =>
    b.env censusTotal=a.env censusTotal+coordinatePrefix ws coord k ∧
    b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b T
  have hp : ∀k b v,P k b→P k (b.set weightIndex v) := by
    rintro k b v ⟨hb,hw,ho,hc',hf⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb,hw,ho,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.pos⟩,
      hf.trans (Fr.set _ _ (by decide))⟩
  have hbody : ∀k (hk : k<ws.length) (b : DS VV),P k b→
      b.env weightIndex=k→b.env weightLength=ws.length→
      C.cw.drop b.cp=intWord ws[k]++((ws.drop (k+1)).flatMap intWord++rest)→
      Hs C readCoordinateWeight b (60*C.cw.length+74) (fun d =>
        P (k+1) d ∧ d.env weightIndex=k ∧ d.env weightLength=ws.length ∧
        d.cp=b.cp+(intWord ws[k]).length) := by
    intro k hk b ⟨hb,hw,ho,hc',hf⟩ hbi hbn hd
    have hbit := coordinatePrefix_le_one ws coord k
    have hlen := len_le_of_drop hd
    have bcoord : b.env coordinate=coord := (hf _ (by decide)).trans hcoord
    refine (readCoordinateWeight_run C b hc' ws[k] _ hd hW hL (by rw [hb]; omega)).mono
      (by omega) ?_
    rintro d ⟨htotal,hcp,hwq,hout,hdc,hfr⟩
    refine ⟨⟨?_,hwq.trans hw,hout.trans ho,hdc,hf.trans (hfr.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))⟩,
      (hfr _ (by decide)).trans hbi,(hfr _ (by decide)).trans hbn,hcp⟩
    rw [htotal,hb,hbi,bcoord,coordinatePrefix_step ws coord k hk]
    omega
  have hwalk := walk (C := C) ws intWord weightIndex weightLength (by decide)
    readCoordinateWeight P (60*C.cw.length+74) rest hp hbody (by omega) a
    ⟨by simp [coordinatePrefix],rfl,rfl,hc,Fr.refl _ _⟩ hi hn hin
  refine hwalk.mono le_rfl ?_
  rintro b ⟨⟨hb,hw,ho,hc',hf⟩,hi',hn',hcursor⟩
  exact ⟨hb,hcursor,hw,ho,hc',hf,hi',hn'⟩

end NearQuarticWires.StageCert.Incidence
