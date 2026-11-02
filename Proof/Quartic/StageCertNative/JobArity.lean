import Proof.Quartic.StageCertNative.CountedSourceBody
import Proof.Quartic.StagePrint.CallArityMemory
import Proof.Quartic.StagePrintContext.Capacity

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCert.Tokens StageLift

/-- `lem:print`, paper/paper.tex: the arity
header is read from the actual retained original call, not provided
with the loop index or native source metadata. -/
def jobArityBody : St VV MM :=
  .seq readCountedIndexedMoment (.seq StagePrint.Header.readCallArity
    (emitNaturalFields [StagePrint.Header.arity]))

noncomputable def jobAritySteps {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  countedReadSteps r.moment (termCount r.base)+100*(r.word.length+1)+100

theorem TermJob.arity_le_word {B1 B2 : ℕ} (r : TermJob B1 B2) :
    r.moment.call.n≤r.word.length := by
  have hn:=StagePrintContext.arity_le_source r.base.prepared
  change r.base.prepared.call.n≤r.base.prepared.word.length at hn
  unfold TermJob.word cachedSourceWord StageCertificateControl.IndexedRequest.baseWord
  simp only [List.length_append]
  exact hn.trans (by omega)

theorem jobArityBody_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=r.word)
    (hwidth : r.word.length+10≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C jobArityBody a (jobAritySteps r) (fun z=>z.out=a.out++natWord r.moment.call.n) := by
  have hread : (countedIndexedWord r.moment (termCount r.base)).length+2≤C.Wd := by
    rw [r.word_layout,List.length_append] at hwidth
    omega
  have hi:=readCountedIndexedMoment_run C r.moment (termCount r.base)
    (StagePrint.Context.word r.base.prepared) a hc (by rw [←r.word_layout];exact hin) hread hempty
  obtain ⟨b,n1,he1,hn1,bd,bcall,_bi,bs,bc⟩:=hi
  have brc : b.rc callStore≤(callWord r.moment.call).length := by
    have hh:=he1.rc_le (by intro store;rw [(hempty store).1,(hempty store).2];rfl) callStore
    simpa only [bcall,List.length_map] using hh
  have hcallLength : (callWord r.moment.call).length≤r.word.length := by
    have hh:=StagePrintContext.call_length_le r.base.prepared
    have hp : r.base.prepared.word.length≤r.word.length := by
      unfold TermJob.word cachedSourceWord StageCertificateControl.IndexedRequest.baseWord
      simp only [List.length_append]
      omega
    exact hh.trans hp
  have hnbl : natBitLength r.moment.call.n≤r.word.length+1 := by
    have hh:=NearCubicGates.Close.Cells.nbl_le_self r.moment.call.n
    exact hh.trans (by have h:=r.arity_le_word;omega)
  unfold jobArityBody
  apply Hx.hs
  refine Hs.then (show Hs C readCountedIndexedMoment a
    (countedReadSteps r.moment (termCount r.base)) (·=b) from ⟨b,n1,he1,hn1,rfl⟩)
    (fun q hq n1a hn1a=>?_)
  subst q
  refine Hs.then (StagePrint.Header.readCallArity_run C r.moment.call b bc bcall (by omega))
    (fun d ⟨dv,_di,doo,_dram,_dsmall,dc,_df⟩ n2 hn2=>?_)
  refine Hs.last (emitNaturalFields_spec C [StagePrint.Header.arity] d dc (r.word.length+1)
    (by intro x hx;simp only [List.mem_singleton] at hx;subst x;decide)
    (by intro x hx;simp only [List.mem_singleton] at hx;subst x;rw [dv];exact hnbl)
    (by omega) (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self))
    (fun z ⟨zo,_zs,_zc,_zf⟩ n3 hn3=>?_)
  have bo : b.out=a.out := congrArg Prod.fst bs
  refine ⟨?_,?_⟩
  · simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,dv,doo,bo] using zo
  · change n3≤1*(40*(r.word.length+1)+43)+1 at hn3
    dsimp only [jobAritySteps]
    omega

/-- `lem:print`, paper/paper.tex: the actual
original arity is framed for the original-arity-first native formatter. -/
def jobArityProgram : St VV MM := .seq initP (StageMain.framedOutputProgram jobArityBody)

theorem jobArityProgram_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (hin : C.inp=r.word) (hwidth : r.word.length+10≤C.Wd) :
    Hs C jobArityProgram (a0 : DS VV MM) (3*jobAritySteps r+8)
      (fun z=>z.out=frame (natWord r.moment.call.n)) := by
  unfold jobArityProgram
  refine (Hs.seq (t2:=3*jobAritySteps r+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=jobArityBody_run C r a hc
    (by simp only [hip,List.drop_zero,hin]) hwidth
    (by intro store;rw [hram,hrc];exact ⟨rfl,rfl⟩)
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame (natWord r.moment.call.n)
  rw [ho,hout,List.nil_append]

noncomputable def jobArityBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM r.word (3*jobAritySteps r+8)

/-- `lem:print` and `prop:time`, paper/paper.tex: a fixed cold ordinary machine reads original n from
its retained original call, including every original source read. -/
noncomputable def jobArityWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (natWord r.moment.call.n)) jobArityBudget :=
  StageFormulaMetadata.wordFunction_of_finite TermJob.word
    (fun r=>frame (natWord r.moment.call.n)) StageRecovery.packetCallee
    jobArityProgram (fun r=>3*jobAritySteps r+8) (fun r=>by
      obtain ⟨b,n,he,hn,ho⟩:=jobArityProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee r.word) r rfl
        (by change r.word.length+10≤100*(r.word.length+1);omega)
      exact ⟨b,n,he,ho,hn⟩)

end NearQuarticWires.StageCertNative
