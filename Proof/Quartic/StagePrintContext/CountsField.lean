import Proof.Quartic.StagePrintContext.EmitCost
import Proof.Quartic.StagePrint.SourceValidity
import Proof.Quartic.StageCert.FrequencyCounts
import Proof.Gates.Cells.Run

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCert.Tokens StageLift

/-- `lem:print`, paper/paper.tex:
the two original occurrence counts and actual radix occupy distinct slots. -/
def radixVar : Fin VV:=95

def countsRegisters : List (Fin VV):=[firstGateCount,atomCount,radixVar]

/-- `sec:params`, paper/paper.tex: the sampler
radix is the actual eighth scalar of the retained public source. -/
theorem retained_radix (p : Cells.Parameters) : (parameterScalars p).getD 7 0=p.N := rfl

/-- `lem:print`, paper/paper.tex:
each occurrence count is physically recovered from its original
frequency, and the actual retained radix is read in binary. -/
def emitCountsField : St VV MM :=
  .seq (readFrequencyCount ⟨14,by decide⟩ firstGateCount)
    (.seq (readFrequencyCount ⟨15,by decide⟩ atomCount)
      (.seq (StageMain.readParameter ⟨7,by decide⟩ radixVar) (framedFields countsRegisters)))

/-- `prop:time`, paper/paper.tex: the census
field pays both original scalar reads, exact bounded count arithmetic,
the radix read and every byte of its real output frame. -/
def countsFieldCost (width : ℕ) : ℕ := 500+3*fieldClock 3 width

/-- `lem:print`, paper/paper.tex:
the census operations preserve all retained affine-header values. -/
def countsScratch : List (Fin VV) :=
  [t2,vJ,c0,atomValue,tupleQuotient,tupleRemainder,firstGateCount,atomCount,radixVar]++
    StagePrint.Header.headerEmitScratch

/-- `lem:print` and `prop:time`, paper/paper.tex: actual public source bytes supply the
original counts and radix, with no decoded census or numeric-value loop. -/
theorem emitCountsField_run (C : Ctx) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (a : DS VV MM)
    (hc : Cst a) (ha : Valid C a) (hstore : a.ram parameterStore=parameterScalars p)
    (hW : 5≤C.Wd) :
    Hs C emitCountsField a (countsFieldCost C.Wd) (fun z=>
      z.out=a.out++frame ([c.first.gates.length,c.second.gates.length,p.N].flatMap
        NearCubicWires.RepairRepresentation.natWord) ∧
      z.ip=a.ip ∧z.ram=a.ram ∧(z.kin,z.kout,z.kc)=(a.kin,a.kout,a.kc) ∧
      Cst z ∧Valid C z ∧Fr a z countsScratch) := by
  have h32 : 32≤2^C.Wd := by
    have hh:=Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) hW
    norm_num at hh
    exact hh
  have hcursor : a.rc parameterStore≤46 := by
    have hh:=ha.rc_le parameterStore
    simpa only [hstore,parameterScalars_length] using hh
  unfold emitCountsField
  apply Hx.hs
  refine Hs.then (StagePrint.source_addValid (by omega) ha
    (readFrequencyCount_run C p ⟨14,by decide⟩ firstGateCount (by decide) (by decide)
      c.first.gates.length a hc hstore (retained_first_frequency c hs) (by change 14<2^C.Wd;omega) hW))
    (fun b ⟨⟨bg,br,bs,bc,bfr⟩,bv⟩ n1 hn1=>?_)
  have bpar : b.ram parameterStore=parameterScalars p := by
    rw [show b.ram=a.ram from congrArg (fun q=>q.2.2.1) bs]
    exact hstore
  refine Hs.then (StagePrint.source_addValid (by omega) bv
    (readFrequencyCount_run C p ⟨15,by decide⟩ atomCount (by decide) (by decide)
      c.second.gates.length b bc bpar (retained_second_frequency c hs) (by change 15<2^C.Wd;omega) hW))
    (fun d ⟨⟨dg,dr,ds,dc,dfr⟩,dv⟩ n2 hn2=>?_)
  have dpar : d.ram parameterStore=parameterScalars p := by
    rw [show d.ram=b.ram from congrArg (fun q=>q.2.2.1) ds]
    exact bpar
  refine Hs.then (StagePrint.source_addValid (by omega) dv
    (StageMain.readParameter_run C p ⟨7,by decide⟩ radixVar d dc dpar
      (by change 7<2^C.Wd;omega) (by decide)))
    (fun e ⟨⟨en,er,es,ec,efr⟩,ev⟩ n3 hn3=>?_)
  have eg1 : e.env firstGateCount=c.first.gates.length := by
    rw [efr _ (by decide),dfr _ (by decide)]
    exact bg
  have eg2 : e.env atomCount=c.second.gates.length := by rw [efr _ (by decide)];exact dg
  have eN : e.env radixVar=p.N := en.trans (retained_radix p)
  have evalues : countsRegisters.map e.env=[c.first.gates.length,c.second.gates.length,p.N] := by
    simp only [countsRegisters,List.map_cons,List.map_nil,eg1,eg2,eN]
  have ePrint:=framedFields_run C countsRegisters e ec ev (by omega) (by decide)
  have heCost:=headerEmitCost_valid C countsRegisters e ev (by omega)
  change StagePrint.Header.headerEmitCost (countsRegisters.map e.env)≤fieldClock 3 C.Wd at heCost
  rw [evalues] at ePrint heCost
  refine Hs.last ePrint (fun z hz n4 hn4=>?_)
  rcases hz with ⟨zo,zi,zr,_zrc,zs,zc,zv,zfr⟩
  have rest:=es.trans (ds.trans bs)
  refine ⟨⟨?_,zi.trans (congrArg (fun q=>q.1) rest),
    zr.trans (congrArg (fun q=>q.2.2.1) rest),
    zs.trans (congrArg (fun q=>(q.2.2.2.2.1,q.2.2.2.2.2.1,q.2.2.2.2.2.2)) rest),zc,zv,?_⟩,?_⟩
  · rw [zo,show e.out=a.out from congrArg (fun q=>q.2.1) rest]
  · exact (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans
      ((efr.weaken (by decide)).trans (zfr.weaken (by intro field hf;exact List.mem_append_right _ hf))))
  · rw [br] at hn2
    rw [dr] at hn3
    change n1≤a.rc parameterStore+7*14+53 at hn1
    change n2≤15+7*15+53 at hn2
    change n3≤16+7*7+13 at hn3
    unfold countsFieldCost
    omega

end NearQuarticWires.StagePrintContext
