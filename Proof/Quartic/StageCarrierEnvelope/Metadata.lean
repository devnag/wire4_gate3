import Proof.Quartic.StageCarrierEnvelope.Prefix
import Proof.Quartic.StageCarrierEnvelope.ColumnCodec
import Proof.Quartic.StagePrintContext.Program

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StagePrint StagePrint.Header StageRecovery.OutputFrame

/-- `lem:print`, paper/paper.tex: source
geometry is acquired once and the original column codec is constructed
with no table, collector, or arithmetic metadata supplier. -/
def metadataBody : St VV MM :=
  .seq baseHeaderProgram (.seq computeFree emitColumnCount)

/-- `prop:time`, paper/paper.tex: actual
original source/header work and every binary column-codec step are paid. -/
noncomputable def metadataBodySteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  baseHeaderCost r.child.call r.child.selected.1 r.child.witness+1+
    (5+1+(100*(r.child.call.n+1)+100))

/-- `lem:print`, paper/paper.tex: the actual
retained source and its physically computed geometry determine exactly
the original column-count codec. -/
theorem metadataBody_run {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : Valid C a)
    (hd : HeaderSourceData (HeaderCall.of_print r) a)
    (hW : r.child.call.n+3≤C.Wd)
    (hcap : 4*(r.child.call.n+1)^2+r.child.call.n+20<2^C.Wd) :
    Hs C metadataBody a (metadataBodySteps r) (fun b=>
      b.out=a.out++natWord r.child.cellCall.ncol ∧ Cst b) := by
  unfold metadataBody
  apply Hx.hs
  refine Hs.then (baseHeaderProgram_run C (HeaderCall.of_print r) a hc ha hd hW hcap)
    (fun b ⟨hb,_br,_bi,bo,_bs,bc,_bv⟩ n1 hn1=>?_)
  have ef:=computeFree_run C r b bc hb.n hb.r hb.s (by
    have hh:=Nat.lt_two_pow_self (n:=C.Wd)
    omega)
  refine Hs.then ef (fun d ⟨df,ds,dc⟩ n2 hn2=>?_)
  refine Hs.last (emitColumnCount_run C r d dc df hW hcap) (fun out ⟨ho,oc⟩ n3 hn3=>?_)
  refine ⟨⟨by rw [ho,ds.out,bo],oc⟩,?_⟩
  unfold metadataBodySteps
  change n1≤baseHeaderCost r.child.call r.child.selected.1 r.child.witness at hn1
  omega

/-- `lem:print`, paper/paper.tex: the actual
cold metadata pass reads the sole compiled carrier input and frames
only the original column codec it physically computes. -/
def metadataProgram : St VV MM := .seq metadataAcquire (framedProgram metadataBody)

/-- `prop:time`, paper/paper.tex: framing and
every sequencing transition are included in the source clock. -/
noncomputable def metadataSteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  metadataReadSteps r+3*metadataBodySteps r+3

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal carrier alone supplies the original
column codec through one cold pass with only finite-prefix arithmetic width. -/
theorem metadataProgram_run {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    Hs (ctxOf StageRecovery.packetCallee metadataSizes (TermsCarrier.word r)) metadataProgram
      (a0 : DS VV MM) (metadataSteps r) (fun b=>b.out=frame (natWord r.child.cellCall.ncol)) := by
  let C:=ctxOf StageRecovery.packetCallee metadataSizes (TermsCarrier.word r)
  have hw:=metadata_width r
  change 100*((StageLift.preparedWordOf r).length+1)^2≤C.Wd at hw
  have hlin : 100*((StageLift.preparedWordOf r).length+1)≤C.Wd := by
    have hh:=Nat.le_self_pow (by decide : (2 : ℕ)≠0) ((StageLift.preparedWordOf r).length+1)
    omega
  have hfinite : StageFormulaMetadata.finiteWidth (prepared r).word.length≤C.Wd := by
    rw [prepared_word]
    exact hlin
  have hcapacity:=StagePrintContext.context_capacity (prepared r)
  have hW : r.child.call.n+3≤C.Wd := hcapacity.2.1.trans hfinite
  have hcap : 4*(r.child.call.n+1)^2+r.child.call.n+20<2^C.Wd :=
    hcapacity.2.2.trans_le (Nat.pow_le_pow_right (by decide) hfinite)
  unfold metadataProgram
  refine (Hs.seq (t2:=3*metadataBodySteps r+2) (metadataAcquire_run C r rfl hlin) ?_).mono
    (by unfold metadataSteps;omega) (fun _ h=>h)
  rintro a ⟨hd,ho,hc,hv⟩
  obtain ⟨b,n,he,hn,hout,_hbc⟩:=metadataBody_run C r a hc hv hd hW hcap
  have hf:=framedProgram_spec he
  have hmark : markedState a=a := by
    unfold markedState markedBits
    simp only [ho,List.flatMap_nil]
    rw [←ho]
  rw [hmark] at hf
  refine ⟨framedState b,3*n+2,hf,by omega,?_⟩
  change frame b.out=frame (natWord r.child.cellCall.ncol)
  rw [hout,ho,List.nil_append]

/-- `prop:time`, paper/paper.tex: the actual
ordinary clock uses the same prefix-derived sizes on the full input,
including its linear input copying and final head reset. -/
noncomputable def metadataBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  langBudget StageRecovery.packetCallee metadataSizes VV MM (TermsCarrier.word r) (metadataSteps r)

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual ordinary program computes the exact
original column codec from the sole original carrier, without supplied metadata. -/
noncomputable def metadataWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) TermsCarrier.word
      (fun r=>frame (natWord r.child.cellCall.ncol)) metadataBudget :=
  wordFunction_of_lang TermsCarrier.word (fun r=>frame (natWord r.child.cellCall.ncol))
    StageRecovery.packetCallee metadataSizes metadataProgram metadataSteps
    (by
      intro r
      obtain ⟨b,n,he,hn,ho⟩:=metadataProgram_run r
      exact ⟨b,n,he,ho,hn⟩)
    (by
      intro r
      have hh:=metadata_width r
      change 1≤ metadataSizes.W (leadOnes (TermsCarrier.word r))
      exact (show 1≤100*((StageLift.preparedWordOf r).length+1)^2 from by
        have hp : 1≤((StageLift.preparedWordOf r).length+1)^2:=Nat.one_le_pow _ _ (by omega)
        omega).trans hh)

end NearQuarticWires.StageCarrierEnvelope
