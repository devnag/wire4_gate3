import Proof.Quartic.StageCert.StructuralFlagList
import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StageGamma.ReadFields
import Proof.Quartic.StageMain.ParameterGet

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: the original test fields and actual
low-first term ordinal are retained in six distinct numeric registers. -/
def momentSourceFields : List (Fin VV) :=
  [sourceTestTag,selectedCircuit,sourceSignOrdinal,requestedChainRow,sourceTestThreshold,sourceTermIndex]

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the six original scalar values are literal fields of the cold request. -/
def MomentRequest.sourceValues {B1 B2 : ℕ} (r : MomentRequest B1 B2) : List ℕ :=
  let t := r.test.metadata r.selected.1
  [t.tag,t.circuit,t.signOrdinal,t.digitOrdinal,t.threshold,r.index.val]

/-- `lem:print`, paper/paper.tex: the suffix
contains exactly the six natural fields consumed by the source parser. -/
theorem MomentRequest.word_source_layout {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.word=Program.prepWord B1 B2 r.call r.witness++r.sourceValues.flatMap natWord := by
  simp only [MomentRequest.word,MomentRequest.sourceValues,StageCertTests.TestMetadata.word,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

/-- `sec:params` and `lem:print`, paper/paper.tex: all retained source data comes from the literal finite
preparation word, including arbitrary proposed witness bits. -/
structure MomentSourceData {B1 B2 : ℕ} (r : MomentRequest B1 B2) (a : DS VV MM) : Prop where
  parameters : a.ram parameterStore=parameterScalars r.selected.1
  factors : a.ram factorStore=r.selected.1.factors
  witness : a.ram witnessStore=r.retainedWitness.map Bool.toNat
  compact : a.ram compactStore=(Program.prepWord B1 B2 r.call r.witness).map Bool.toNat
  compactLength : a.env StageMain.Compact.compactLength=(Program.prepWord B1 B2 r.call r.witness).length
  compactCursor : a.rc compactStore=(Program.prepWord B1 B2 r.call r.witness).length
  witnessCursor : a.rc witnessStore≤r.retainedWitness.length
  factorCursor : a.rc factorStore≤r.selected.1.factors.length
  parameterCursor : a.rc parameterStore=8
  fields : ∀i : Fin 6,a.env momentSourceFields[i]=r.sourceValues[i]
  base : a.env patternBase=r.selected.1.N

/-- `lem:print`, paper/paper.tex: the source
physically parses the finite prep word, six natural fields and the
selected radix N before any structural factor is computed. -/
def readMomentSource : St VV MM :=
  .seq initializeCompact (.seq (StageGamma.readFields momentSourceFields)
    (readParameter ⟨7,by decide⟩ patternBase))

/-- `prop:time`, paper/paper.tex: the source
parser's exact cost includes original preparation, literal field reads
and the paid selected-parameter rewind and scan. -/
noncomputable def MomentRequest.readSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  initializeCost r.call r.selected.1 r.retainedWitness
    (Program.prepWord B1 B2 r.call r.witness).length+
    StageGamma.readFieldsCost r.sourceValues+120

/-- `lem:print` and `prop:time`, paper/paper.tex: cold original bytes suffice for every retained source
field; no initialized records, decoded mask or Formula is an input. -/
theorem readMomentSource_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=r.word++rest) (hwidth : r.word.length+2≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C readMomentSource a r.readSteps (fun z=>
      MomentSourceData r z ∧ z.ip=a.ip+r.word.length ∧
      (z.out,z.kin,z.kout,z.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst z) := by
  let prep := compactInput r.call r.selected.1 r.retainedWitness
  have hprep : Program.prepWord B1 B2 r.call r.witness=prep :=
    prepWord_eq_compact r.dispatched r.witness
  have hlayout := r.word_source_layout
  have hpwidth : prep.length+2≤C.Wd := by
    rw [hlayout,hprep,List.length_append] at hwidth
    omega
  have hvalues : ∀value∈r.sourceValues,natBitLength value+2≤C.Wd := by
    intro value hv
    have hword : (natWord value).length≤(r.sourceValues.flatMap natWord).length := by
      obtain ⟨l,t,heq⟩ := List.mem_iff_append.mp hv
      rw [heq]
      simp only [List.flatMap_append,List.flatMap_cons,List.length_append]
      omega
    have hnat := NearCubicGates.Close.Dispatch.natBitLength_le_len value
    rw [hlayout,List.length_append] at hwidth
    omega
  have hWd : 3≤C.Wd := by
    have hlen : 1≤r.word.length := by
      rw [hlayout]
      simp only [MomentRequest.sourceValues,List.flatMap_cons,List.flatMap_nil,
        List.length_append,List.length_nil,natWord_length]
      omega
    omega
  have h7 : 7<2^C.Wd := lt_of_lt_of_le (by decide : 7<2^3)
    (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hWd)
  obtain ⟨hprefix,hfit,hbits,hprime,hfactor⟩ :=
    compact_decoder_bounds r.call r.selected.1 r.retainedWitness C.Wd hpwidth
  have hi := initialize_run C r.call r.selected.1 prep.length r.retainedWitness
    (r.sourceValues.flatMap natWord++rest) a hc
    (by simpa only [hlayout,hprep,List.append_assoc] using hin)
    hprefix hfit hbits hpwidth ⟨hprime,hfactor⟩ (fun store _=>hempty store)
  obtain ⟨b,n,he,hn,hb⟩ := hi
  rcases hb with ⟨bip,bd,blen,bram,brc,bs,bc,bf⟩
  have hrc (store : Fin MM) : b.rc store≤(b.ram store).length :=
    he.rc_le (by intro store; rw [(hempty store).1,(hempty store).2]; rfl) store
  have bp : b.rc parameterStore≤46 := by
    have hh := hrc parameterStore
    rw [bd.scalarFields,parameterScalars_length] at hh
    exact hh
  have bw : b.rc witnessStore≤r.retainedWitness.length := by
    have hh := hrc witnessStore
    simpa only [bd.witnessBits,List.length_map] using hh
  have br : b.rc factorStore≤r.selected.1.factors.length := by
    have hh := hrc factorStore
    simpa only [bd.factorFields] using hh
  have bin : C.inp.drop b.ip=r.sourceValues.flatMap natWord++rest := by
    rw [bip,←List.drop_drop,hin,hlayout]
    rw [hprep,List.append_assoc]
    change (prep++(r.sourceValues.flatMap natWord++rest)).drop prep.length=_
    exact List.drop_left
  have hf := StageGamma.readFields_spec C momentSourceFields (by decide) (by
    intro x hx
    simp only [momentSourceFields,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
    r.sourceValues rfl b bc rest bin hvalues
  unfold readMomentSource
  apply Hx.hs
  refine Hs.then (show Hs C initializeCompact a
    (initializeCost r.call r.selected.1 r.retainedWitness prep.length) (·=b) from
    ⟨b,n,he,hn,rfl⟩) (fun q hq n1 hn1=>?_)
  subst q
  refine Hs.then hf (fun d ⟨dv,di,ds,dc,df⟩ n2 hn2=>?_)
  have dram : d.ram=b.ram := congrArg (fun q=>q.2.1) ds
  have drc : d.rc=b.rc := congrArg (fun q=>q.2.2.1) ds
  refine Hs.last (readParameter_run C r.selected.1 ⟨7,by decide⟩ patternBase d dc
    (by rw [dram]; exact bd.scalarFields) h7 (by decide))
    (fun z ⟨zv,zrc,zs,zc,zf⟩ n3 hn3=>?_)
  have zram : z.ram=d.ram := congrArg (fun q=>q.2.2.1) zs
  have zip : z.ip=d.ip := congrArg (fun q=>q.1) zs
  have zrcOther (store : Fin MM) (hne : store≠parameterStore) : z.rc store=d.rc store := by
    have hh := congrArg (fun q=>q.2.2.2.1 store) zs
    simpa only [StageMain.parameterRest,Function.update_of_ne hne] using hh
  refine ⟨⟨⟨by rw [zram,dram]; exact bd.scalarFields,
    by rw [zram,dram]; exact bd.factorFields,
    by rw [zram,dram]; exact bd.witnessBits,
    by rw [zram,dram,bram,hprep],
    (zf _ (by decide)).trans ((df _ (by decide)).trans (by rw [hprep]; exact blen)),
    by rw [zrcOther compactStore (by decide),drc,brc,hprep],
    by rw [zrcOther witnessStore (by decide),drc]; exact bw,
    by rw [zrcOther factorStore (by decide),drc]; exact br,zrc,
    fun i=>(zf _ (by fin_cases i <;> decide)).trans (dv i),zv⟩,?_,?_,zc⟩,?_⟩
  · rw [zip,di,bip,hlayout,List.length_append,hprep]
    dsimp only [prep]
    omega
  · have zsmall := congrArg (fun q=>(q.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1,q.2.2.2.2.2.2)) zs
    have dsmall := congrArg (fun q=>(q.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) ds
    exact zsmall.trans (dsmall.trans bs)
  · change n3≤d.rc parameterStore+7*7+13 at hn3
    rw [drc] at hn3
    unfold MomentRequest.readSteps
    rw [hprep]
    omega

end NearQuarticWires.StageCert.Tokens
