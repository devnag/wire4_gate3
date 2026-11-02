import Proof.Quartic.StageCertNative.TermCount
import Proof.Quartic.StageCert.MomentFramedMachine
import Proof.Quartic.StageGamma.Retain
import Proof.Quartic.StageLift.Literal

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCertificateControl StageCert.Tokens

/-- `lem:print`, paper/paper.tex: the selected
population or closed-walk source always has an actual first term. -/
theorem termCount_pos {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : 0<termCount r := by
  have hs := Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  have hN : 0<r.prepared.selected.1.N := lt_of_lt_of_le (by decide : 0<2)
    (Cells.ParameterRules.N_ge_two hs)
  unfold termCount
  cases actualOrdinal r <;> exact Nat.pow_pos hN

noncomputable def zeroMoment {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : MomentRequest B1 B2 :=
  actualMoment r ⟨0,termCount_pos r⟩

/-- `lem:print`, paper/paper.tex: appending a
literal zero ordinal permits reuse of the actual six-field source
reader while leaving the BASE input unchanged. -/
theorem zeroMoment_word {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (zeroMoment r).word=r.baseWord++natWord 0 := actualMoment_word r _

/-- `lem:print` and `prop:time`, paper/paper.tex: the binary zero ordinal is emitted by literal
ordinary operations; its value is not a supplied loop count. -/
def zeroOrdinalProgram : St VV MM :=
  .seq initP (StageLift.emitLiteral (frame (natWord 0)))

theorem zeroOrdinalProgram_run (C : Ctx) (hW : 2≤C.Wd) :
    Hs C zeroOrdinalProgram (a0 : DS VV MM) 30 (fun b=>b.out=frame (natWord 0)) := by
  unfold zeroOrdinalProgram
  refine (Hs.seq (t2:=2*(frame (natWord 0)).length+1)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hW)))
    (fun a ⟨hc,_,_,_,hout,_,_,_,_⟩=>?_)).mono (by decide) (fun _ h=>h)
  refine (StageLift.emitLiteral_spec C (frame (natWord 0)) a hc).mono le_rfl ?_
  intro b hb
  rw [hb.1,hout]
  rfl

noncomputable def zeroOrdinalBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM r.baseWord 30

noncomputable def zeroOrdinalWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun _=>frame (natWord 0)) zeroOrdinalBudget :=
  StageFormulaMetadata.wordFunction_of_finite IndexedRequest.baseWord (fun _=>frame (natWord 0))
    StageRecovery.packetCallee zeroOrdinalProgram (fun _=>30) (fun r=>by
      obtain ⟨b,n,he,hn,ho⟩ := zeroOrdinalProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee r.baseWord)
        (by change 2≤100*(r.baseWord.length+1); omega)
      exact ⟨b,n,he,ho,hn⟩)

/-- `lem:print` and `prop:time`, paper/paper.tex: the original complete BASE bytes are physically
retained and the literal first ordinal appended before source decoding. -/
noncomputable def firstTermSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (zeroMoment r).word)
      (fun r=>2*StageGamma.retainedCost (input:=IndexedRequest.baseWord)
        (cache:=fun _ : IndexedRequest B1 B2=>natWord 0) (budget:=zeroOrdinalBudget) r+2) := by
  convert StageGamma.retainedWordFunction (zeroOrdinalWordFunction B1 B2) using 1
  funext r
  rw [zeroMoment_word]

end NearQuarticWires.StageCertNative
