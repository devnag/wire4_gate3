import Proof.Quartic.StageCertNative.CountSource
import Proof.Quartic.StageCertNative.ExactSource
import Proof.Quartic.StagePrintContext.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens StageCertificateControl StageMain.Compact

/-- `lem:print`, paper/paper.tex: actual source
acquisition is followed by a paid bit-for-bit copy of its retained
original preparation, without reading any following Gamma stream. -/
def prepCopyBody : St VV MM := .seq readMomentSource
  (StageMainMask.emitStoredWord compactStore compactLength)

noncomputable def prepCopySteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  r.readSteps+9*(Program.prepWord B1 B2 r.call r.witness).length+7

theorem prepCopyBody_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=r.word)
    (hwidth : r.word.length+4≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C prepCopyBody a (prepCopySteps r) (fun z=>
      z.out=a.out++Program.prepWord B1 B2 r.call r.witness) := by
  unfold prepCopyBody
  apply Hx.hs
  refine Hs.then (readMomentSource_run C r [] a hc (by simpa only [List.append_nil] using hin)
    (by omega) hempty) (fun b ⟨bd,_bi,bs,bc⟩ n1 hn1=>?_)
  have boutput : b.out=a.out := congrArg Prod.fst bs
  have hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^C.Wd :=
    lt_of_le_of_lt (r.prep_length_le.trans (by omega)) Nat.lt_two_pow_self
  refine Hs.last (StageMainMask.emitStoredWord_run C compactStore compactLength (by decide)
    (Program.prepWord B1 B2 r.call r.witness) b bc bd.compact bd.compactLength hfit)
    (fun z ⟨zo,_zip,_kin,_ram,_rc,_kout,_kc,_zc,_zf⟩ n2 hn2=>?_)
  rw [bd.compactCursor] at hn2
  exact ⟨by rw [zo,boutput],by dsimp only [prepCopySteps];omega⟩

def prepCopyProgram : St VV MM := .seq initP (StageMain.framedOutputProgram prepCopyBody)

theorem prepCopyProgram_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (hin : C.inp=r.word) (hwidth : r.word.length+4≤C.Wd) :
    Hs C prepCopyProgram (a0 : DS VV MM) (3*prepCopySteps r+8)
      (fun z=>z.out=frame (Program.prepWord B1 B2 r.call r.witness)) := by
  unfold prepCopyProgram
  refine (Hs.seq (t2:=3*prepCopySteps r+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=prepCopyBody_run C r a hc
    (by simp only [hip,List.drop_zero,hin]) hwidth
    (by intro store;rw [hram,hrc];exact ⟨rfl,rfl⟩)
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame (Program.prepWord B1 B2 r.call r.witness)
  rw [ho,hout,List.nil_append]

noncomputable def prepCopyBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM r.word (3*prepCopySteps r+8)

/-- `lem:print` and `prop:time`, paper/paper.tex: the finite original prep is extracted by an actual
cold parser and stored-word copy, with its entire physical clock. -/
noncomputable def prepCopyWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.word
      (fun r=>frame (Program.prepWord B1 B2 r.call r.witness)) prepCopyBudget :=
  StageFormulaMetadata.wordFunction_of_finite MomentRequest.word
    (fun r=>frame (Program.prepWord B1 B2 r.call r.witness)) StageRecovery.packetCallee
    prepCopyProgram (fun r=>3*prepCopySteps r+8) (fun r=>by
      obtain ⟨b,n,he,hn,ho⟩:=prepCopyProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee r.word) r rfl
        (by change r.word.length+4≤100*(r.word.length+1);omega)
      exact ⟨b,n,he,ho,hn⟩)

noncomputable def basePrepBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  4*(2*StageGamma.retainedCost (input:=IndexedRequest.baseWord)
    (cache:=fun _ : IndexedRequest B1 B2=>natWord 0) (budget:=zeroOrdinalBudget) r+2)+
    4*prepCopyBudget (zeroMoment r)+12

/-- `lem:print`, paper/paper.tex: BASE's actual
preparation is isolated from the unchanged five-field metadata by one
fixed source machine, before computing the shared native context. -/
noncomputable def basePrepWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame r.prepared.word) basePrepBudget :=
  Program.WordFunction.pipe (firstTermSourceWordFunction B1 B2)
    (restrictWordFunction (prepCopyWordFunction B1 B2) (fun r=>zeroMoment r))

noncomputable def baseContextBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  4*basePrepBudget r+4*(StagePrintContext.contextProducer B1 B2).1 r.prepared+12

/-- `lem:print`, paper/paper.tex: one actual
context is computed from BASE's original finite source by the checked
cold context machine, without supplied headers, pools or geometry. -/
noncomputable def baseContextWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (StagePrint.Context.word r.prepared)) baseContextBudget :=
  Program.WordFunction.pipe (basePrepWordFunction B1 B2)
    (restrictWordFunction (StagePrintContext.contextProducer B1 B2).2
      (fun r : IndexedRequest B1 B2=>r.prepared))

end NearQuarticWires.StageCertNative
