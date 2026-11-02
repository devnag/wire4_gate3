import Proof.Quartic.StageCert.MomentSourceCopy

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCert.Tokens StageMain StageMain.Compact StageLift

/-- `lem:print`, paper/paper.tex: the counted term
index precedes the unchanged original preparation and five test fields. -/
def indexedMomentFields : List (Fin VV) :=
  [sourceTestTag,selectedCircuit,sourceSignOrdinal,requestedChainRow,sourceTestThreshold]

def indexedMomentValues {B1 B2 : ℕ} (r : MomentRequest B1 B2) : List ℕ :=
  let t:=r.test.metadata r.selected.1
  [t.tag,t.circuit,t.signOrdinal,t.digitOrdinal,t.threshold]

noncomputable def indexedMomentWord {B1 B2 : ℕ} (r : MomentRequest B1 B2) : List Bool :=
  natWord r.index.val++Program.prepWord B1 B2 r.call r.witness++
    (indexedMomentValues r).flatMap natWord

theorem indexedMomentWord_length {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (indexedMomentWord r).length=r.word.length := by
  rw [r.word_source_layout]
  simp [indexedMomentWord,indexedMomentValues,MomentRequest.sourceValues]
  omega

/-- `lem:print`, paper/paper.tex: actual indexed
term input is decoded using the original finite preparation parser. -/
def readIndexedMoment : St VV MM :=
  .seq (StageGamma.readField sourceTermIndex)
    (.seq initializeCompact (.seq (StageGamma.readFields indexedMomentFields)
      (readParameter ⟨7,by decide⟩ patternBase)))

noncomputable def indexedReadSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  30*natBitLength r.index.val+32+
    initializeCost r.call r.selected.1 r.retainedWitness
      (Program.prepWord B1 B2 r.call r.witness).length+
    StageGamma.readFieldsCost (indexedMomentValues r)+120

/-- `lem:print` and `prop:time`, paper/paper.tex: decoding the loop's prefix index reconstructs exactly
the same original source data, with no supplied records or masks. -/
theorem readIndexedMoment_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=indexedMomentWord r++rest)
    (hwidth : r.word.length+2≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C readIndexedMoment a (indexedReadSteps r) (fun z=>
      MomentSourceData r z ∧ z.ip=a.ip+(indexedMomentWord r).length ∧
      (z.out,z.kin,z.kout,z.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst z) := by
  let prep:=compactInput r.call r.selected.1 r.retainedWitness
  have hprep : Program.prepWord B1 B2 r.call r.witness=prep :=
    prepWord_eq_compact r.dispatched r.witness
  have hw := hwidth
  rw [←indexedMomentWord_length r] at hw
  have hpwidth : prep.length+2≤C.Wd := by
    dsimp only [indexedMomentWord] at hw
    rw [List.length_append,List.length_append,hprep] at hw
    omega
  have hiv : natBitLength r.index.val+2≤C.Wd := by
    have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_len r.index.val
    dsimp only [indexedMomentWord] at hw
    rw [List.length_append,List.length_append] at hw
    omega
  have hvalues : ∀value∈indexedMomentValues r,natBitLength value+2≤C.Wd := by
    intro value hv
    have hword : (natWord value).length≤((indexedMomentValues r).flatMap natWord).length := by
      obtain ⟨l,t,heq⟩:=List.mem_iff_append.mp hv
      rw [heq]
      simp only [List.flatMap_append,List.flatMap_cons,List.length_append]
      omega
    have hn:=NearCubicGates.Close.Dispatch.natBitLength_le_len value
    dsimp only [indexedMomentWord] at hw
    rw [List.length_append,List.length_append] at hw
    omega
  have hWd : 3≤C.Wd := by
    have hpos : 1≤(natWord r.index.val).length := by
      rw [natWord_length]
      omega
    dsimp only [indexedMomentWord] at hw
    rw [List.length_append,List.length_append] at hw
    omega
  have h7 : 7<2^C.Wd := lt_of_lt_of_le (by decide : 7<2^3)
    (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hWd)
  have hfirst:=StageGamma.readField_spec C sourceTermIndex (by decide) (by decide)
    a hc r.index.val
    (prep++(indexedMomentValues r).flatMap natWord++rest)
    (by simpa only [indexedMomentWord,hprep,List.append_assoc] using hin) hiv
  unfold readIndexedMoment
  apply Hx.hs
  refine Hs.then hfirst (fun d ⟨dv,di,ds,dc,df⟩ n0 hn0=>?_)
  have din : C.inp.drop d.ip=prep++((indexedMomentValues r).flatMap natWord++rest) := by
    rw [di,←List.drop_drop,hin]
    simp only [indexedMomentWord,hprep,List.append_assoc,List.drop_left]
  have dram : d.ram=a.ram := congrArg (fun q=>q.2.1) ds
  have drc : d.rc=a.rc := congrArg (fun q=>q.2.2.1) ds
  obtain ⟨hprefix,hfit,hbits,hprime,hfactor⟩:=
    compact_decoder_bounds r.call r.selected.1 r.retainedWitness C.Wd hpwidth
  have hi:=initialize_run C r.call r.selected.1 prep.length r.retainedWitness
    ((indexedMomentValues r).flatMap natWord++rest) d dc din
    hprefix hfit hbits hpwidth ⟨hprime,hfactor⟩
    (by intro store _; rw [dram,drc]; exact hempty store)
  obtain ⟨b,n1,he1,hn1,hb⟩:=hi
  rcases hb with ⟨bip,bd,blen,bram,brc,bs,bc,bf⟩
  refine Hs.then (show Hs C initializeCompact d
      (initializeCost r.call r.selected.1 r.retainedWitness prep.length) (·=b) from
      ⟨b,n1,he1,hn1,rfl⟩) (fun q hq n1a hn1a=>?_)
  subst q
  have bindex : b.env sourceTermIndex=r.index.val :=
    (bf _ (by decide)).trans dv
  have hrc (store : Fin MM) : b.rc store≤(b.ram store).length := by
    exact he1.rc_le (by intro store; rw [dram,drc,(hempty store).1,(hempty store).2];rfl) store
  have bp : b.rc parameterStore≤46 := by
    have hh:=hrc parameterStore
    rw [bd.scalarFields,parameterScalars_length] at hh
    exact hh
  have bw : b.rc witnessStore≤r.retainedWitness.length := by
    simpa only [bd.witnessBits,List.length_map] using hrc witnessStore
  have br : b.rc factorStore≤r.selected.1.factors.length := by
    simpa only [bd.factorFields] using hrc factorStore
  have bin : C.inp.drop b.ip=(indexedMomentValues r).flatMap natWord++rest := by
    rw [bip,←List.drop_drop,din]
    exact List.drop_left
  have hf:=StageGamma.readFields_spec C indexedMomentFields (by decide) (by
    intro x hx
    simp only [indexedMomentFields,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> decide)
    (indexedMomentValues r) rfl b bc rest bin hvalues
  refine Hs.then hf (fun e ⟨ev,ei,es,ec,ef⟩ n2 hn2=>?_)
  have eram : e.ram=b.ram := congrArg (fun q=>q.2.1) es
  have erc : e.rc=b.rc := congrArg (fun q=>q.2.2.1) es
  refine Hs.last (readParameter_run C r.selected.1 ⟨7,by decide⟩ patternBase e ec
    (by rw [eram];exact bd.scalarFields) h7 (by decide))
    (fun z ⟨zv,zrc,zs,zc,zf⟩ n3 hn3=>?_)
  have zram : z.ram=e.ram := congrArg (fun q=>q.2.2.1) zs
  have zip : z.ip=e.ip := congrArg (fun q=>q.1) zs
  have zrcOther (store : Fin MM) (hne : store≠parameterStore) : z.rc store=e.rc store := by
    have hh:=congrArg (fun q=>q.2.2.2.1 store) zs
    simpa only [StageMain.parameterRest,Function.update_of_ne hne] using hh
  have zfields (i : Fin 6) : z.env momentSourceFields[i]=r.sourceValues[i] := by
    fin_cases i
    all_goals first
      | exact (zf _ (by decide)).trans (ev ⟨0,by decide⟩)
      | exact (zf _ (by decide)).trans (ev ⟨1,by decide⟩)
      | exact (zf _ (by decide)).trans (ev ⟨2,by decide⟩)
      | exact (zf _ (by decide)).trans (ev ⟨3,by decide⟩)
      | exact (zf _ (by decide)).trans (ev ⟨4,by decide⟩)
      | exact (zf _ (by decide)).trans ((ef _ (by decide)).trans bindex)
  refine ⟨⟨⟨by rw [zram,eram];exact bd.scalarFields,
    by rw [zram,eram];exact bd.factorFields,
    by rw [zram,eram];exact bd.witnessBits,
    by rw [zram,eram,bram,hprep],
    (zf _ (by decide)).trans ((ef _ (by decide)).trans (by rw [hprep];exact blen)),
    by rw [zrcOther compactStore (by decide),erc,brc,hprep],
    by rw [zrcOther witnessStore (by decide),erc];exact bw,
    by rw [zrcOther factorStore (by decide),erc];exact br,zrc,zfields,zv⟩,?_,?_,zc⟩,?_⟩
  · rw [zip,ei,bip,di]
    simp only [indexedMomentWord,List.length_append,hprep]
    dsimp only [prep]
    omega
  · have zsmall:=congrArg (fun q=>(q.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1,q.2.2.2.2.2.2)) zs
    have esmall:=congrArg (fun q=>(q.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) es
    have dsmall:=congrArg (fun q=>(q.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) ds
    exact zsmall.trans (esmall.trans (bs.trans dsmall))
  · change n3≤e.rc parameterStore+7*7+13 at hn3
    rw [erc] at hn3
    dsimp only [indexedReadSteps]
    rw [hprep]
    omega

end NearQuarticWires.StageCertNative
