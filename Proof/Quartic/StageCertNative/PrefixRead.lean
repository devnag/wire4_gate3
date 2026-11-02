import Proof.Quartic.StageCertNative.NFirstSource
import Proof.Quartic.StageCertNative.CountedRead

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens StageLift

/-- `lem:print`, paper/paper.tex: the computed
original-arity prefix selects the workspace; its scalar is physically
read before the unchanged actual counted source. -/
def readPrefixSource : St VV MM :=
  .seq (StageGamma.readField StagePrint.Header.arity) readCountedIndexedMoment

noncomputable def prefixReadSteps {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  30*natBitLength r.moment.call.n+33+countedReadSteps r.moment (termCount r.base)

theorem readPrefixSource_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=nFirstWord r)
    (hword : (nFirstWord r).length+10≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C readPrefixSource a (prefixReadSteps r) (fun z=>
      MomentSourceData r.moment z ∧
      z.ram callStore=(NearCubicGates.Close.Interfaces.callWord r.moment.call).map Bool.toNat ∧
      C.inp.drop z.ip=StagePrint.Context.word r.base.prepared ∧
      (z.out,z.kin,z.kout,z.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst z) := by
  have hnbl : natBitLength r.moment.call.n+2≤C.Wd := by
    have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_len r.moment.call.n
    dsimp only [nFirstWord] at hword
    rw [List.length_append] at hword
    omega
  unfold readPrefixSource
  apply Hx.hs
  refine Hs.then (StageGamma.readField_spec C StagePrint.Header.arity (by decide) (by decide)
    a hc r.moment.call.n r.word hin hnbl) (fun b ⟨_bv,bi,bs,bc,_bf⟩ n1 hn1=>?_)
  have bin : C.inp.drop b.ip=countedIndexedWord r.moment (termCount r.base)++
      StagePrint.Context.word r.base.prepared := by
    rw [bi,←List.drop_drop,hin]
    simpa only [nFirstWord,List.drop_left] using r.word_layout
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
  have brc : b.rc=a.rc := congrArg (fun q=>q.2.2.1) bs
  have hread : (countedIndexedWord r.moment (termCount r.base)).length+2≤C.Wd := by
    rw [nFirstWord,List.length_append,r.word_layout,List.length_append] at hword
    omega
  refine Hs.last (readCountedIndexedMoment_run C r.moment (termCount r.base)
    (StagePrint.Context.word r.base.prepared) b bc bin hread
    (by intro store;rw [bram,brc];exact hempty store))
    (fun z ⟨zd,zcall,zi,zs,zc⟩ n2 hn2=>?_)
  refine ⟨⟨zd,zcall,?_,?_,zc⟩,by dsimp only [prefixReadSteps];omega⟩
  · rw [zi,←List.drop_drop,bin]
    exact List.drop_left
  · have bsmall:=congrArg (fun q=>(q.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) bs
    exact zs.trans bsmall

end NearQuarticWires.StageCertNative
