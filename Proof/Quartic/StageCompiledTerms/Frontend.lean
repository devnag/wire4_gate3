import Proof.Quartic.StageCompiledTerms.CarrierCodec
import Proof.Quartic.StageCompiledTerms.Prefix
import Proof.Quartic.StageCompiledTerms.Acquire
import Proof.Quartic.StageCompiledTerms.MeasuredFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the actual
streaming adapter uses one fixed sixteen-register workspace. -/
def frontRegisters : Fin 16 ↪ Fin 16 := Function.Embedding.refl _

/-- Step 3 and `lem:print`, paper/paper.tex: acquire one source, copy one context, isolate and
tag all its actual packets, then seal the whole physical batch input. -/
def carrierFrontend : WM 3 16 :=
  .seq acquireCarrier
    (.seq (preparePrefix 1 2 frontRegisters)
      (.seq (.whs 1 (tagPacket 1 2 3 2 4)) (measuredFrame 2 3 15 2 3 14 13)))

/-- `prop:time`, paper/paper.tex: capacity
bounds real source/output counters and only the finite preparation
length decoder; no walk index magnitude is decoded numerically. -/
def RawCarrier.frontCapacity (r : RawCarrier) : ℕ :=
  100*(r.word.length+r.batchWord.length+r.packets.length+1)+
    2^(natBitLength r.preparation.length+1)

/-- `prop:time`, paper/paper.tex: the adapter
clock is linear in complete source and batch bytes, plus the once-only
preparation-length decoder. No compiler clock is squared. -/
def RawCarrier.frontSteps (r : RawCarrier) : ℕ :=
  23*r.word.length+5+prefixCost r.preparation r.packets.length+
    (400*((r.packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length+r.packets.length)+1)+
      (200*r.batchWord.length+50)+10

/-- Step 3, `lem:print` and `prop:time`, paper/paper.tex: the actual complete streaming
adapter derives every tag, packet boundary and copied byte from the
literal one-copy source carrier, including all original zero walks. -/
theorem carrierFrontend_spec (r : RawCarrier) :
    ∃ final,WExec r.frontCapacity carrierFrontend (idealStart 3 16 r.word (fun _=>0))
      final r.frontSteps ∧ final.st 3=frame r.batchWord := by
  let cap:=r.frontCapacity
  let raw:=r.packets.flatMap StageFormulaMetadata.RawWalkPacket.word
  let context:=natWord r.preparation.length++r.preparation
  let count:=natWord r.packets.length
  have hlinear : 100*(r.word.length+r.batchWord.length+r.packets.length+1)≤cap :=
    Nat.le_add_right _ _
  have hinput : r.word.length≤cap := by omega
  have hword : r.word=context++count++raw := by rfl
  have hbatch : r.batchWord=frame context++count++taggedPacketWords r.packets := by rfl
  have hlength : r.word.length=context.length+count.length+raw.length := by
    rw [hword];simp only [List.length_append]
  have hbatchLength : r.batchWord.length=(frame context++count).length+(taggedPacketWords r.packets).length := by
    rw [hbatch];simp only [List.length_append]
  let a:=idealStart 3 16 r.word (fun _=>0)
  have eAcquire:=acquireCarrier_spec r.word cap hinput
  let b:=(a.sets 1 r.word).seth 0 (2*r.word.length+1)
  have hbSource : b.st (1:Fin 4)=[]++natWord r.preparation.length++r.preparation++
      natWord r.packets.length++raw := by simp [b,a,hword,context,count]
  have hbHead : b.sh (1:Fin 4)=0 := rfl
  have hbOut : b.sh (2:Fin 4)=(b.st 2).length := rfl
  have hbZero : ∀ j : Fin 16,j≠3→b.val (frontRegisters j)=0 := by intro j _;rfl
  have hprefCap : b.val (frontRegisters 3)+
      20*((natWord r.preparation.length).length+r.preparation.length+(natWord r.packets.length).length+1)+
        2^(natBitLength r.preparation.length+1)≤cap := by
    have h : 20*((natWord r.preparation.length).length+r.preparation.length+count.length+1)≤
        100*(r.word.length+r.batchWord.length+r.packets.length+1) := by
      dsimp only [context] at hlength
      rw [List.length_append] at hlength
      omega
    simpa only [b,a,idealStart,WState.seth_val,WState.sets_val,frontRegisters,
      Function.Embedding.refl_apply,Nat.zero_add,count,cap,RawCarrier.frontCapacity] using Nat.add_le_add_right h
        (2^(natBitLength r.preparation.length+1))
  obtain ⟨c,ePrefix,hcSource,hcHead,hcOut,hcOutputHead,hcCounter,hc2,hc4,hc13,hc14,hc15,hcOther⟩:=
    preparePrefix_spec cap (1:Fin 4) 2 frontRegisters (by decide)
      r.preparation r.packets.length [] raw b hbSource hbHead hbOut hbZero hprefCap
  have hcCounter' : c.val (3:Fin 16)=(frame context++count).length := by
    simpa only [b,a,idealStart,WState.seth_val,WState.sets_val,frontRegisters,
      Function.Embedding.refl_apply,Nat.zero_add,context,count] using hcCounter
  change c.val (2:Fin 16)=0 at hc2
  change c.val (4:Fin 16)=0 at hc4
  have hcInput : c.st (1:Fin 4)=(context++count)++raw := by
    rw [hcSource];exact hword
  have hcPosition : c.sh (1:Fin 4)=(context++count).length := by
    simpa only [List.length_nil,Nat.zero_add,context,count,List.append_assoc] using hcHead
  have hcOutput : c.st (2:Fin 4)=frame context++count := by
    simpa [b,a,idealStart,context,count] using hcOut
  have hcLoopCap : c.val (3:Fin 16)+20*(raw.length+r.packets.length+1)≤cap := by
    rw [hcCounter']
    have hpre : (frame context++count).length≤r.batchWord.length := by omega
    omega
  have ePackets:=tagPackets_spec cap (1:Fin 4) 2 (3:Fin 16) 2 4
    (by decide) (by decide) (by decide) (by decide) r.packets (context++count) c
    hcInput hcPosition hcOutputHead hc2 hc4 hcLoopCap
  let d:=(appendO c 2 3 (taggedPacketWords r.packets)).seth 1
    ((context++count).length+raw.length)
  have hdWord : d.st (2:Fin 4)=r.batchWord := by
    simp only [d,WState.seth_st,appendO_st,Function.update_self,hcOutput,hbatch,List.append_assoc]
  have hdHead : d.sh (2:Fin 4)=r.batchWord.length := by
    simp only [d,WState.seth_sh,Function.update_of_ne (by decide : (2:Fin 4)≠1),
      appendO_sh,Function.update_self,hcOutputHead,hcOutput,hbatch,List.length_append]
  have hd3 : d.val (3:Fin 16)=r.batchWord.length := by
    simp only [d,WState.seth_val,appendO_val,Function.update_self,hcCounter',hbatch,List.length_append]
  have hd2 : d.val (2:Fin 16)=0 := by
    simp only [d,WState.seth_val,appendO_val,Function.update_of_ne (by decide : (2:Fin 16)≠3),hc2]
  have hd13 : d.val (13:Fin 16)=0 := by
    simpa only [d,WState.seth_val,appendO_val,Function.update_of_ne (by decide : (13:Fin 16)≠3),
      frontRegisters,Function.Embedding.refl_apply,b,a,idealStart,WState.sets_val] using hc13
  have hd14 : d.val (14:Fin 16)=0 := by
    simpa only [d,WState.seth_val,appendO_val,Function.update_of_ne (by decide : (14:Fin 16)≠3),
      frontRegisters,Function.Embedding.refl_apply,b,a,idealStart,WState.sets_val] using hc14
  have hd15 : d.val (15:Fin 16)=0 := by
    simpa only [d,WState.seth_val,appendO_val,Function.update_of_ne (by decide : (15:Fin 16)≠3),
      frontRegisters,Function.Embedding.refl_apply,b,a,idealStart,WState.sets_val] using hc15
  have hdOut : d.st (3:Fin 4)=[] ∧ d.sh (3:Fin 4)=0 := by
    have h:=hcOther 3 (by decide) (by decide)
    simpa [d,appendO,b,a,idealStart] using h
  obtain ⟨final,eFrame,hfinal⟩:=measuredFrame_spec cap (2:Fin 4) 3 (15:Fin 16) 2 3 14 13
    (by decide) (by decide) r.batchWord d hdWord hdHead
    (by rw [hdOut.1,hdOut.2];rfl) hd3 hd2 hd14 hd13
    (by rw [hd15];omega)
  refine ⟨final,?_,?_⟩
  · exact (eAcquire.seq (ePrefix.seq (ePackets.seq eFrame))).mono (by unfold RawCarrier.frontSteps;omega)
  · simpa only [hdOut.1,List.nil_append] using hfinal

end NearQuarticWires.StageCompiledTerms
