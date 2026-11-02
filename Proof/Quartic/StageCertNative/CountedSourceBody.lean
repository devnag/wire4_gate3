import Proof.Quartic.StageCertNative.CountedRead
import Proof.Quartic.StageCertNative.TermJob

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens StageCertificateControl

/-- `lem:print`, paper/paper.tex: each term of
the counted shared-source loop physically recovers its original exact
source while leaving the once-computed context as an unread suffix. -/
theorem TermJob.word_layout {B1 B2 : ℕ} (r : TermJob B1 B2) :
    r.word=countedIndexedWord r.moment (termCount r.base)++StagePrint.Context.word r.base.prepared := by
  unfold TermJob.word cachedSourceWord countedIndexedWord TermJob.moment indexedMomentValues actualMoment
  rw [actualOrdinal_metadata]
  simp only [IndexedRequest.baseWord,StageCertTests.PreparedScheduleRequest.word,
    StageCertTests.TestMetadata.word,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

theorem countedIndexedWord_length {B1 B2 : ℕ} (r : MomentRequest B1 B2) (extra : ℕ) :
    (countedIndexedWord r extra).length=r.word.length+(natWord extra).length := by
  rw [r.word_source_layout]
  simp only [countedIndexedWord,indexedMomentValues,MomentRequest.sourceValues,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
  omega

def countedSourceBody : St VV MM := .seq readCountedIndexedMoment emitMomentSourceCopy

noncomputable def countedSourceSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) (extra : ℕ) : ℕ :=
  countedReadSteps r extra+9*(Program.prepWord B1 B2 r.call r.witness).length+
    6*(40*r.word.length+43)+9

theorem countedSourceBody_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (extra : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=countedIndexedWord r extra++rest)
    (hwidth : (countedIndexedWord r extra).length+4≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C countedSourceBody a (countedSourceSteps r extra) (fun z=>z.out=a.out++r.word) := by
  have hlen : r.word.length≤(countedIndexedWord r extra).length := by
    rw [countedIndexedWord_length];omega
  unfold countedSourceBody
  apply Hx.hs
  refine Hs.then (readCountedIndexedMoment_run C r extra rest a hc hin (by omega) hempty)
    (fun b ⟨bd,_bcall,_bi,bs,bc⟩ n1 hn1=>?_)
  have boutput : b.out=a.out := congrArg Prod.fst bs
  have hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^C.Wd :=
    lt_of_le_of_lt (r.prep_length_le.trans (by omega)) Nat.lt_two_pow_self
  refine Hs.last (emitMomentSourceCopy_run C r b bc bd r.word.length
    (fun value hv=>r.value_bits value hv) (by omega)
    (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self) hfit)
    (fun z ⟨zo,_zs,_zc,_zf⟩ n2 hn2=>?_)
  exact ⟨by rw [zo,boutput],by dsimp only [countedSourceSteps];omega⟩

def countedSourceProgram : St VV MM :=
  .seq initP (StageMain.framedOutputProgram countedSourceBody)

theorem countedSourceProgram_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (hin : C.inp=r.word) (hwidth : r.word.length+4≤C.Wd) :
    Hs C countedSourceProgram (a0 : DS VV MM)
      (3*countedSourceSteps r.moment (termCount r.base)+8)
      (fun z=>z.out=frame r.moment.word) := by
  unfold countedSourceProgram
  refine (Hs.seq (t2:=3*countedSourceSteps r.moment (termCount r.base)+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  have hcap : (countedIndexedWord r.moment (termCount r.base)).length+4≤C.Wd := by
    rw [r.word_layout,List.length_append] at hwidth
    omega
  obtain ⟨b,n,he,hn,ho⟩:=countedSourceBody_run C r.moment (termCount r.base)
    (StagePrint.Context.word r.base.prepared) a hc
    (by simp only [hip,List.drop_zero,hin,r.word_layout]) hcap
    (by intro store;rw [hram,hrc];exact ⟨rfl,rfl⟩)
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame r.moment.word
  rw [ho,hout,List.nil_append]

end NearQuarticWires.StageCertNative
