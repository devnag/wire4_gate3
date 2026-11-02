import Proof.Quartic.StageCertificateControl.NativePrefixLoad
import Proof.Quartic.StagePrint.CallStates

/-!
# Exact retained binary header and native-call exterior states

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: native-bank
erasure retains the binary threshold and measured input-copy distance. -/
def nativePrefixClearedState (p : Program) (threshold : ℕ) (input : List Bool) :
    WState (p.tapeCount+11) 32 :=
  (nativePrefixReadState p threshold input).setv 7 (2*input.length)

/-- `prop:time`, paper/paper.tex: the
actual loaded native bank contains its exact original input frame. -/
theorem nativePrefixLoaded_eq_bank (p : Program) (threshold : ℕ) (input : List Bool) :
    nativePrefixLoadedState p threshold input=
      (nativePrefixClearedState p threshold input).sets (indexedSite p).input (frame input) := by
  have h0 : (indexedSite p).input≠indexedExternal p 0 := indexedBank_external_ne p (inTape p) 0
  apply WState.eq
  · funext i
    by_cases hi : i=(indexedSite p).input
    · subst i
      simp only [nativePrefixLoadedState,nativePrefixClearedState,nativePrefixReadState,
        WState.setv_sh,WState.seth_sh,WState.sets_sh,Function.update_self,
        Function.update_of_ne h0,startState]
    · simp [nativePrefixLoadedState,nativePrefixClearedState,Function.update_of_ne hi]
  · simp [nativePrefixLoadedState,nativePrefixClearedState]
  · rfl
  · rfl

/-- `prop:time`, paper/paper.tex: cleanup
removes the actual native input and every work tape while preserving
the separate binary header and original source offset. -/
theorem nativePrefixCleanLoaded_eq (p : Program) (threshold : ℕ) (input : List Bool) :
    cleanState (indexedSite p) (nativePrefixLoadedState p threshold input)=
      nativePrefixClearedState p threshold input := by
  rw [nativePrefixLoaded_eq_bank]
  change cleanState (indexedSite p)
    ((nativePrefixClearedState p threshold input).sets ((indexedSite p).bank (inTape p)) (frame input))=_
  rw [StagePrint.cleanState_set_bank]
  apply StagePrint.cleanState_self
  · intro j
    have h1 := indexedBank_external_ne p j 1
    have hv : (indexedBank p j).val≠0 := by change 11+j.val≠0;omega
    have h0 : indexedBank p j≠(0 : Fin (p.tapeCount+12)) := by
      intro h;exact hv (congrArg Fin.val h)
    simp [nativePrefixClearedState,nativePrefixReadState,indexedSite,startState,h1,hv,h0]
  · intro j
    have h0 := indexedBank_external_ne p j 0
    simp [nativePrefixClearedState,nativePrefixReadState,indexedSite,startState,Function.update_of_ne h0]
  · simp [nativePrefixClearedState,nativePrefixReadState,indexedSite,startState,indexedExternal]
  · simp [nativePrefixClearedState,nativePrefixReadState,indexedSite,startState,indexedExternal]

/-- `prop:time`, paper/paper.tex: the actual
copied native frame retains its physical output-byte counter. -/
def nativePrefixCopiedState (p : Program) (threshold : ℕ) (input payload : List Bool) :
    WState (p.tapeCount+11) 32 :=
  appendO (nativePrefixClearedState p threshold input) (indexedExternal p 2) 14 (frame payload)

/-- `prop:time`, paper/paper.tex: consuming
the actual copied-byte count returns the retained native frame to head
zero without an output-length oracle. -/
def nativePrefixReadyState (p : Program) (threshold : ℕ) (input payload : List Bool) :
    WState (p.tapeCount+11) 32 :=
  ((nativePrefixCopiedState p threshold input payload).setv 14 0).seth (indexedExternal p 2) 0

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual native call/append/erase
state depends only on the retained original bytes and unchanged native
output, independently of erased internal tapes and running time. -/
theorem nativePrefixCallPost_eq (p : Program) (threshold : ℕ) (input payload : List Bool)
    (tapes : Fin p.tapeCount→List Bool) (steps : ℕ) :
    cleanState (indexedSite p)
      (appendO (calledState (indexedSite p) (nativePrefixLoadedState p threshold input)
        tapes input.length steps) (indexedExternal p 2) 14 (frame payload))=
      nativePrefixCopiedState p threshold input payload := by
  rw [StagePrint.callAppendPost_eq (indexedSite p) _ tapes input.length steps
    (indexedExternal p 2) 14 (frame payload) (fun j => indexedBank_external_ne p j 2)
    (by intro h;have hh := congrArg Fin.val h;change 2=8 at hh;omega)
    (by intro h;have hh := congrArg Fin.val h;change 2=9 at hh;omega)]
  rw [nativePrefixCleanLoaded_eq]
  rfl

/-- `prop:time`, paper/paper.tex: the
retained binary header and unchanged native frame both have their real
heads at zero after the paid native-frame return. -/
theorem nativePrefixReady_frames (p : Program) (threshold : ℕ) (input payload : List Bool) :
    let σ := nativePrefixReadyState p threshold input payload
    σ.st (indexedExternal p 1)=frame (RepairRepresentation.natWord threshold) ∧
    σ.sh (indexedExternal p 1)=0 ∧
    σ.st (indexedExternal p 2)=frame payload ∧ σ.sh (indexedExternal p 2)=0 ∧
    σ.val 19=0 ∧ σ.val 20=0 := by
  dsimp only
  and_intros
  all_goals simp [nativePrefixReadyState,nativePrefixCopiedState,nativePrefixClearedState,
    nativePrefixReadState,startState,appendO,indexedExternal]

/-- `prop:time`, paper/paper.tex: all
native bank tapes contain the actual cold base input and have their
physical heads at zero before the whole-table call. -/
theorem nativePrefixLoaded_bank (p : Program) (threshold : ℕ) (input : List Bool) :
    (∀ j,(nativePrefixLoadedState p threshold input).st (indexedBank p j)=p.inputTapes input j) ∧
      (∀ j,(nativePrefixLoadedState p threshold input).sh (indexedBank p j)=0) := by
  constructor
  · intro j
    rw [nativePrefixLoaded_eq_bank]
    by_cases hj : j=inTape p
    · subst j;simp [Site.input,indexedSite,Program.inputTapes,inTape]
    · have hji : indexedBank p j≠(indexedSite p).input := by
        intro h;apply hj;exact (indexedSite p).bank_inj h
      have h1 := indexedBank_external_ne p j 1
      have hv : (indexedBank p j).val≠0 := by change 11+j.val≠0;omega
      have h0 : indexedBank p j≠(0 : Fin (p.tapeCount+12)) := by
        intro h;exact hv (congrArg Fin.val h)
      have hjv : j.val≠0 := by intro h;apply hj;apply Fin.ext;exact h
      simp [nativePrefixClearedState,nativePrefixReadState,Function.update_of_ne hji,
        startState,Program.inputTapes,hjv,hv,h0,h1]
  · intro j
    rw [nativePrefixLoaded_eq_bank]
    have h0 := indexedBank_external_ne p j 0
    simp [nativePrefixClearedState,nativePrefixReadState,startState,Function.update_of_ne h0]

/-- `prop:time`, paper/paper.tex: retained
external words are exactly the original source and binary header;
every other external work stream is genuinely empty. -/
theorem nativePrefixCleared_external (p : Program) (threshold : ℕ) (input : List Bool) (i : Fin 11) :
    (nativePrefixClearedState p threshold input).st (indexedExternal p i)=
      (if i.val=1 then frame (RepairRepresentation.natWord threshold)
       else if i.val=0 then frame (RepairRepresentation.natWord threshold++input) else []) ∧
    (nativePrefixClearedState p threshold input).sh (indexedExternal p i)=
      (if i.val=0 then 2*(RepairRepresentation.natWord threshold).length else 0) := by
  constructor
  · by_cases hi : i.val=1
    · have he : indexedExternal p i=indexedExternal p 1 := Fin.ext hi
      simp [nativePrefixClearedState,nativePrefixReadState,he,hi]
    · have he : indexedExternal p i≠indexedExternal p 1 := by
        intro h;exact hi (congrArg (fun x : Fin (p.tapeCount+12) => x.val) h)
      simp [nativePrefixClearedState,nativePrefixReadState,Function.update_of_ne he,
        startState,indexedExternal,hi]
  · change Function.update (fun _ => 0) (indexedExternal p 0)
      (2*(RepairRepresentation.natWord threshold).length) (indexedExternal p i)=_
    by_cases hi : i.val=0
    · have he : indexedExternal p i=indexedExternal p 0 := Fin.ext hi
      simp [he,hi]
    · have he : indexedExternal p i≠indexedExternal p 0 := by
        intro h;exact hi (congrArg (fun x : Fin (p.tapeCount+12) => x.val) h)
      simp [Function.update_of_ne he,hi]

/-- `prop:time`, paper/paper.tex: the only
retained pre-call register values measure original encoded bytes;
no register contains the potentially enormous threshold value. -/
theorem nativePrefixCleared_values (p : Program) (threshold : ℕ) (input : List Bool) (i : Fin 32) :
    (nativePrefixClearedState p threshold input).val i=
      (if i=7 then 2*input.length else if i=4 then 2*(RepairRepresentation.natWord threshold).length else 0) := by
  simp [nativePrefixClearedState,nativePrefixReadState,startState,Function.update_apply]

end NearQuarticWires.StageCertificateControl
