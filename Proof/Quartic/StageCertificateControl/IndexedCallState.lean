import Proof.Quartic.StageCertificateControl.IndexedLoad
import Proof.Quartic.StagePrint.CallStates

/-!
# Exact exterior state after the actual scheduler call and erase

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
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

/-- `prop:time`, paper/paper.tex: the
original indexed source and measured preparation-copy count survive
scheduler-bank erasure, while every reusable bank tape is empty. -/
noncomputable def indexedClearedState {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    WState (p.tapeCount+11) 32 :=
  (indexedReadState p r).setv 21 (2*r.prepared.word.length)

/-- `prop:time`, paper/paper.tex: the
actual loaded bank differs from the retained exterior only by the
literal framed preparation on the scheduler's input tape. -/
theorem indexedLoadedState_eq_bank {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    indexedLoadedState p r=(indexedClearedState p r).sets (indexedSite p).input (frame r.prepared.word) := by
  have hne := indexedBank_external_ne p (inTape p) 0
  apply WState.eq
  · funext i
    by_cases hi : i=(indexedSite p).input
    · subst i
      have hi : (indexedSite p).input≠indexedExternal p 0 := hne
      simp only [indexedLoadedState,indexedClearedState,indexedReadState,WState.setv_sh,
        WState.seth_sh,WState.sets_sh,Function.update_self,Function.update_of_ne hi,startState]
    · simp [indexedLoadedState,indexedClearedState,Function.update_of_ne hi]
  · simp [indexedLoadedState,indexedClearedState]
  · rfl
  · rfl

/-- `prop:time`, paper/paper.tex: erasing
the actual loaded scheduler bank returns precisely the retained
original-source state, including its real preparation-offset head. -/
theorem indexedCleanLoaded_eq {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    cleanState (indexedSite p) (indexedLoadedState p r)=indexedClearedState p r := by
  rw [indexedLoadedState_eq_bank]
  change cleanState (indexedSite p)
    ((indexedClearedState p r).sets ((indexedSite p).bank (inTape p)) (frame r.prepared.word))=_
  rw [StagePrint.cleanState_set_bank]
  apply StagePrint.cleanState_self
  · intro j
    have hn : (indexedBank p j).val≠0 := by change 11+j.val≠0;omega
    have hb : indexedBank p j≠(0 : Fin (p.tapeCount+12)) := by
      intro h;exact hn (congrArg Fin.val h)
    simp [indexedClearedState,indexedReadState,startState,indexedSite,hn,hb]
  · intro j
    have hn := indexedBank_external_ne p j 0
    simp [indexedClearedState,indexedReadState,startState,indexedSite,Function.update_of_ne hn]
  · simp [indexedClearedState,indexedReadState,startState,indexedSite,indexedExternal]
  · simp [indexedClearedState,indexedReadState,startState,indexedSite,indexedExternal]

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the entire copied schedule has a concrete
external frame and actual byte counter, independent of the erased
scheduler's final internal tapes and running time. -/
noncomputable def indexedSchedulerCopyState {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    WState (p.tapeCount+11) 32 :=
  appendO (indexedClearedState p r) (indexedExternal p 1) 10 (frame r.prepared.output)

/-- `prop:time`, paper/paper.tex: the
actual call/append/erase post-state is exactly the deterministic
exterior schedule-copy state; no internal computational residue is free. -/
theorem indexedCallPost_eq {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2)
    (tapes : Fin p.tapeCount→List Bool) (steps : ℕ) :
    cleanState (indexedSite p)
      (appendO (calledState (indexedSite p) (indexedLoadedState p r) tapes r.prepared.word.length steps)
        (indexedExternal p 1) 10 (frame r.prepared.output))=indexedSchedulerCopyState p r := by
  rw [StagePrint.callAppendPost_eq (indexedSite p) (indexedLoadedState p r) tapes
    r.prepared.word.length steps (indexedExternal p 1) 10 (frame r.prepared.output)
    (fun j => indexedBank_external_ne p j 1)
    (by intro h;have hh := congrArg Fin.val h;change 1=8 at hh;omega)
    (by intro h;have hh := congrArg Fin.val h;change 1=9 at hh;omega)]
  rw [indexedCleanLoaded_eq]
  rfl

/-- `prop:time`, paper/paper.tex: the
retained source state has exactly the original indexed input, its
preparation offset, and otherwise empty external work streams. -/
theorem indexedClearedState_external {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) (i : Fin 11) :
    (indexedClearedState p r).st (indexedExternal p i)=
      (if i.val=0 then frame r.word else []) ∧
    (indexedClearedState p r).sh (indexedExternal p i)=
      (if i.val=0 then 2*(RepairRepresentation.natWord r.index.val).length else 0) := by
  constructor
  · rfl
  · change Function.update (fun _ => 0) (indexedExternal p 0)
      (2*(RepairRepresentation.natWord r.index.val).length) (indexedExternal p i)=_
    by_cases hz : i.val=0
    · have hi : indexedExternal p i=indexedExternal p 0 := Fin.ext hz
      simp [hi,hz]
    · have hi : indexedExternal p i≠indexedExternal p 0 := by
        intro h;exact hz (congrArg (fun x : Fin (p.tapeCount+12) => x.val) h)
      simp [Function.update_of_ne hi,hz]

/-- `prop:time`, paper/paper.tex: the
retained exterior scalar values are only the actual index and measured
preparation copy distance. All scheduler-call scratch is zero. -/
theorem indexedClearedState_values {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) (i : Fin 32) :
    (indexedClearedState p r).val i=
      (if i=21 then 2*r.prepared.word.length else if i=4 then r.index.val else 0) := by
  simp [indexedClearedState,indexedReadState,startState,Function.update_apply]

end NearQuarticWires.StageCertificateControl
