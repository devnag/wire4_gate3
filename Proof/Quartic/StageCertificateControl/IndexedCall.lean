import Proof.Quartic.StageCertificateControl.IndexedCallState
import Proof.Wire_3_5.PrimTReadEq

/-!
# Execute the actual cold scheduler in the indexed preprocessing bank

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the indexed preprocessing invokes the actual
cold scheduler, copies its complete output frame, and physically erases
the entire computational bank before any metadata is selected. -/
theorem indexedScheduler_call {B1 B2 : ℕ} (r : IndexedRequest B1 B2) (cap : ℕ)
    (hcall : 2*r.prepared.word.length+2+framedScheduleBudget r.prepared≤cap)
    (hcopy : (frame r.prepared.output).length+1≤cap) :
    let p := (framedScheduleWordFunction B1 B2).program
    ∃ τ, WXExec cap (StagePrint.callAppendProgram (indexedSite p) (indexedExternal p 1) 10)
      (indexedLoadedState p r) τ
      (StagePrint.callAppendCost r.prepared.word.length (framedScheduleBudget r.prepared)) ∧
      SimW (indexedSchedulerCopyState p r) τ := by
  let f := framedScheduleWordFunction B1 B2
  let p := f.program
  let s := indexedSite p
  let σ := indexedLoadedState p r
  have hout (i : Fin 11) : indexedExternal p i≠s.input :=
    (indexedBank_external_ne p (NearCubicGates.Close.WorkerArith.inTape p) i).symm
  have es (i : Fin 11) : σ.st (indexedExternal p i)=
      (if i.val=0 then frame r.word else []) := by
    dsimp only [σ]
    rw [indexedLoadedState_eq_bank]
    have hi : indexedExternal p i≠(indexedSite p).input := hout i
    simp only [WState.sets_st,Function.update_of_ne hi]
    exact (indexedClearedState_external p r i).1
  have eh (i : Fin 11) : σ.sh (indexedExternal p i)=
      (if i.val=0 then 2*(RepairRepresentation.natWord r.index.val).length else 0) := by
    dsimp only [σ]
    rw [indexedLoadedState_eq_bank]
    exact (indexedClearedState_external p r i).2
  have hv (i : Fin 32) : σ.val i=
      (if i=21 then 2*r.prepared.word.length else if i=4 then r.index.val else 0) := by
    dsimp only [σ]
    rw [indexedLoadedState_eq_bank]
    exact indexedClearedState_values p r i
  have hT : σ.st s.tally=[] := by change σ.st (indexedExternal p 8)=[];simpa using es 8
  have hTh : σ.sh s.tally=0 := by change σ.sh (indexedExternal p 8)=0;simpa using eh 8
  have hG : σ.st s.guard=[] := by change σ.st (indexedExternal p 9)=[];simpa using es 9
  have hGh : σ.sh s.guard=0 := by change σ.sh (indexedExternal p 9)=0;simpa using eh 9
  have hL : σ.st s.ruler=[] := by change σ.st (indexedExternal p 10)=[];simpa using es 10
  have hLh : σ.sh s.ruler=0 := by change σ.sh (indexedExternal p 10)=0;simpa using eh 10
  have hdT : indexedExternal p 1≠s.tally := by
    intro h;have hh := congrArg Fin.val h;change 1=8 at hh;omega
  have hdG : indexedExternal p 1≠s.guard := by
    intro h;have hh := congrArg Fin.val h;change 1=9 at hh;omega
  have hdL : indexedExternal p 1≠s.ruler := by
    intro h;have hh := congrArg Fin.val h;change 1=10 at hh;omega
  obtain ⟨tapes,steps,τ,hsteps,he,hs⟩ := StagePrint.callAppend_exec f r.prepared cap s
    (indexedExternal p 1) 10 (fun j => indexedBank_external_ne p j 1) hdT hdG (by change (10 : Fin 32)≠0;decide) σ
    (indexedLoadedState_bank p r).1 (indexedLoadedState_bank p r).2
    hT hTh hG hGh (by rw [hL];exact nil_blank) hLh
    (by intro i;fin_cases i <;> simp [s,indexedSite,indexedSiteRegs,hv]) hdL
    (by rw [es 1,eh 1];rfl) hcall
    (by rw [hv 10];simpa using hcopy)
  refine ⟨τ,he,?_⟩
  rw [indexedCallPost_eq p r tapes steps] at hs
  exact hs

end NearQuarticWires.StageCertificateControl
