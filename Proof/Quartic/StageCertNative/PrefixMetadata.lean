import Proof.Quartic.StageCertNative.PrefixRead
import Proof.Quartic.StageCertNative.PrefixOutput

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCert.Tokens StageLift

def prefixMetadataProgram (B1 : ℕ) : St VV MM :=
  .seq readPrefixSource (.seq StagePrint.Header.readCallArity
    (.seq computeMomentDegree (computeNativeBits B1)))

noncomputable def prefixMetadataSteps {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  prefixReadSteps r+r.word.length+30*natBitLength r.moment.call.n+nativeBitsSteps B1+500

/-- `lem:print`, paper/paper.tex: every field
of the exact native formatter is loaded or computed from the literal
original preparation, actual loop index and once-cached context. -/
theorem prefixMetadataProgram_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=nFirstWord r)
    (hword : (nFirstWord r).length+10≤C.Wd)
    (hroom : Cells.nativeCertificateBits B1 r.moment.call.n+nativeBitsFactor B1+
      nativeBitsExponentValue B1+r.moment.call.n+r.moment.packet.degree+100<2^C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C (prefixMetadataProgram B1) a (prefixMetadataSteps r) (fun z=>
      PrefixOutputReady C r z ∧ z.out=a.out ∧ Cst z) := by
  obtain ⟨b,n1,he1,hn1,bd,bcall,bsrc,bs,bc⟩:=
    readPrefixSource_run C r a hc hin hword hempty
  have bindex : b.env sourceTermIndex=r.index.val := bd.fields ⟨5,by decide⟩
  have bvalid : ∀store,b.rc store≤(b.ram store).length :=
    he1.rc_le (by intro store;rw [(hempty store).1,(hempty store).2];rfl)
  have brc : b.rc callStore≤(callWord r.moment.call).length := by
    simpa only [bcall,List.length_map] using bvalid callStore
  have hcallLength : (callWord r.moment.call).length≤r.word.length := by
    have hh:=StagePrintContext.call_length_le r.base.prepared
    have hp : r.base.prepared.word.length≤r.word.length := by
      unfold TermJob.word cachedSourceWord StageCertificateControl.IndexedRequest.baseWord
      simp only [List.length_append]
      omega
    exact hh.trans hp
  have hnbl : natBitLength r.moment.call.n+2≤C.Wd := by
    have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_len r.moment.call.n
    have hlen : (natWord r.moment.call.n).length≤(nFirstWord r).length := by
      unfold nFirstWord
      simp only [List.length_append]
      omega
    omega
  obtain ⟨d,n2,he2,hn2,dn,di,doo,dram,_dsmall,dc,df⟩:=
    StagePrint.Header.readCallArity_run C r.moment.call b bc bcall hnbl
  have dparams : d.ram parameterStore=parameterScalars r.moment.selected.1 := by
    rw [dram]
    exact bd.parameters
  have drc : d.rc parameterStore≤46 := by
    have hh:=he2.rc_le bvalid parameterStore
    rw [dparams,parameterScalars_length] at hh
    exact hh
  have dindex : d.env sourceTermIndex=r.index.val := (df _ (by decide)).trans bindex
  unfold prefixMetadataProgram
  apply Hx.hs
  refine Hs.then (show Hs C readPrefixSource a (prefixReadSteps r) (·=b) from
    ⟨b,n1,he1,hn1,rfl⟩) (fun q hq n1a hn1a=>?_)
  subst q
  refine Hs.then (show Hs C StagePrint.Header.readCallArity b
    (b.rc callStore+30*natBitLength r.moment.call.n+40) (·=d) from
    ⟨d,n2,he2,hn2,rfl⟩) (fun q hq n2a hn2a=>?_)
  subst q
  refine Hs.then (computeMomentDegree_run C r.moment.selected.1 d dc dparams
    (by omega) (by change r.moment.packet.degree<2^C.Wd;omega))
    (fun e ⟨ed,_erc,es,ec,ef⟩ n3 hn3=>?_)
  have en : e.env StagePrint.Header.arity=r.moment.call.n := (ef _ (by decide)).trans dn
  have ei : e.env sourceTermIndex=r.index.val := (ef _ (by decide)).trans dindex
  have edegree : e.env degreeVar=r.moment.packet.degree := ed
  have eip : e.ip=d.ip := congrArg Prod.fst es
  have eout : e.out=d.out := congrArg (fun q=>q.2.1) es
  refine Hs.last (computeNativeBits_run C B1 r.moment.call.n e ec en (by omega))
    (fun z ⟨zbits,zsh,zc,zf⟩ n4 hn4=>?_)
  have zip : z.ip=e.ip := congrArg Prod.fst zsh
  have zout : z.out=e.out := congrArg (fun q=>q.2.1) zsh
  refine ⟨⟨⟨(zf _ (by decide)).trans en,(zf _ (by decide)).trans ei,
    (zf _ (by decide)).trans edegree,zbits,by rw [zip,eip,di];exact bsrc⟩,
    zout.trans (eout.trans (doo.trans (congrArg Prod.fst bs))),zc⟩,?_⟩
  unfold prefixMetadataSteps
  omega

end NearQuarticWires.StageCertNative
