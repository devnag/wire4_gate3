import Proof.Quartic.StageCarrierEnvelope.Layout
import Proof.Quartic.StageCarrierEnvelope.Source
import Proof.Quartic.StageCarrierEnvelope.SkipPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: the
bounded physical counters depend on actual byte lengths and the
finite preparation length; no modulus or column magnitude is reserved. -/
noncomputable def envelopeCapacity {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  100*((StagePrint.TermsCarrier.word r).length+2^(natBitLength (StageLift.preparedWordOf r).length+1)+r.child.call.n+10)

noncomputable def prefixSteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  (natBitLength (StageLift.preparedWordOf r).length+2)*(40*2^natBitLength (StageLift.preparedWordOf r).length+40)+
    100*((StageLift.preparedWordOf r).length+((firstFields r).flatMap natWord).length+1)

noncomputable def bodySteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  200*((StagePrint.TermsCarrier.word r).length+1)+1+prefixSteps r+1+
    1000*((natWord (r.prime^r.child.selected.1.e)).length+(frame (StagePrint.TermsCarrier.word r)).length+
      (frame (natWord r.child.cellCall.ncol)).length+1)

/-- `lem:print`, paper/paper.tex: the actual
source is measured once, the genuine first metadata prefix is passed,
and the unchanged envelope is physically emitted. -/
noncomputable def envelopeBody (B1 B2 : ℕ) :
    WM ((metadataWordFunction B1 B2).program.tapeCount+3) 16 :=
  .seq (acquireCarrier 0 1 0 8 9)
    (.seq (skipCarrierPrefix 1) (loadedEnvelope (sourceMap (metadataWordFunction B1 B2).program)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the real once-only metadata reply and original
carrier realize the complete immutable envelope with all copies paid. -/
theorem envelopeBody_run {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (a : WState ((metadataWordFunction B1 B2).program.tapeCount+3) 16) (ha : BankReady r a) :
    ∃ b, WExec (envelopeCapacity r) (envelopeBody B1 B2) a b (bodySteps r) ∧
      b.st (bankOut (metadataWordFunction B1 B2).program.tapeCount)=frame (StagePrint.CarrierEnvelope.word r) := by
  let f:=metadataWordFunction B1 B2
  let t:=f.program.tapeCount
  let I:=(StagePrint.TermsCarrier.word r).length
  let prep:=StageLift.preparedWordOf r
  let F:=((firstFields r).flatMap natWord).length
  have haout : a.st (bankOut t)=[]:=ha.output
  have haoutHead : a.sh (bankOut t)=0:=ha.outputHead
  have hacol : a.st (bankMap t f.program.outputTape)=frame (natWord r.child.cellCall.ncol):=ha.column
  have hacolHead : a.sh (bankMap t f.program.outputTape)=0:=ha.columnHead
  have hprefix:=prefix_length_le_carrier r
  have hPF : prep.length+F≤I := by
    change (firstPrefix r).length≤I at hprefix
    simp only [firstPrefix,List.length_append] at hprefix
    dsimp only [prep,F,I]
    omega
  have hq:=modulus_length_le_carrier r
  change (natWord (r.prime^r.child.selected.1.e)).length≤I at hq
  have hcol:=column_codec_length r
  have hpow : 0≤2^(natBitLength prep.length+1):=Nat.zero_le _
  have h10 : (1 : Fin (t+4))≠0 := by simp
  have hout1 : bankOut t≠(1 : Fin (t+4)) := by simp [bankOut]
  have hbank1:=(bankMap_off t f.program.outputTape).2.1
  have ea:=acquireCarrier_run (envelopeCapacity r) (0 : Fin (t+4)) 1 (0 : Fin 16) 8 9
    (by simp) (by decide) (by decide) (by decide) (StagePrint.TermsCarrier.word r) a
    ha.source ha.sourceHead ha.raw ha.rawHead (ha.regs 0) (ha.regs 8) (ha.regs 9)
    (by change 2*I+4≤100*(I+2^(natBitLength prep.length+1)+r.child.call.n+10);omega)
  let b:=(a.sets 1 (StagePrint.TermsCarrier.word r)).setv (8 : Fin 16) I
  have eb:=skipCarrierPrefix_run (envelopeCapacity r) (1 : Fin (t+4)) (bankOut t) hout1.symm
    prep (firstFields r) (by rfl) (natWord (r.prime^r.child.selected.1.e)++firstRest r) b
    (by simp only [b,WState.setv_st,WState.sets_st,Function.update_self];rw [carrier_first_modulus];simp only [firstPrefix,prep,List.append_assoc])
    (by simp [b,ha.rawHead])
    (by simp [b,Function.update_of_ne hout1,haoutHead,haout])
    (by intro i hi;simp only [b,WState.setv_val,Function.update_of_ne hi,WState.sets_val];exact ha.regs i)
    (by change 2^(natBitLength prep.length+1)+prep.length+F+10≤100*(I+2^(natBitLength prep.length+1)+r.child.call.n+10);omega)
  let c:=firstModulusState (1 : Fin (t+4)) b prep (firstFields r)
  have hcs : c.st 1=firstPrefix r++natWord (r.prime^r.child.selected.1.e)++firstRest r := by
    simp only [c,firstModulusState,WState.setv_st,WState.seth_st,b,WState.sets_st,Function.update_self]
    exact carrier_first_modulus r
  obtain ⟨last,ec,hout⟩:=loadedEnvelope_run (envelopeCapacity r) (sourceMap f.program)
    (r.prime^r.child.selected.1.e) r.child.cellCall.ncol (StagePrint.TermsCarrier.word r)
    (firstPrefix r) (firstRest r) c
    hcs
    (by change c.sh 1=(firstPrefix r).length;simp [c,firstModulusState,firstPrefix,prep,List.length_append,Nat.add_assoc])
    (by change c.st 0=frame (StagePrint.TermsCarrier.word r);simp [c,firstModulusState,b,ha.source])
    (by change c.sh 0=0;simp [c,firstModulusState,b,ha.sourceHead])
    (by change c.st (bankMap t f.program.outputTape)=_;simp [c,firstModulusState,b,Function.update_of_ne hbank1,hacol])
    (by change c.sh (bankMap t f.program.outputTape)=0;simp [c,firstModulusState,b,Function.update_of_ne hbank1,hacolHead])
    (by change c.st (bankOut t)=[];simp [c,firstModulusState,b,Function.update_of_ne hout1,haout])
    (by change c.sh (bankOut t)=0;simp [c,firstModulusState,b,Function.update_of_ne hout1,haoutHead])
    (by simp [c,firstModulusState,b,ha.regs])
    (by simp [c,firstModulusState,b,ha.regs])
    (by
      change prep.length+F+8*((natWord (r.prime^r.child.selected.1.e)).length+
        (frame (StagePrint.TermsCarrier.word r)).length+(frame (natWord r.child.cellCall.ncol)).length+10)≤_
      simp only [frame_length]
      unfold envelopeCapacity
      change _≤100*(I+2^(natBitLength prep.length+1)+r.child.call.n+10)
      omega)
  refine ⟨last,(ea.seq (eb.seq ec)).mono (by dsimp only [bodySteps,prefixSteps,prep];omega),?_⟩
  exact hout

end NearQuarticWires.StageCarrierEnvelope
