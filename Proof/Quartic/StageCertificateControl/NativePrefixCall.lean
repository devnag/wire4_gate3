import Proof.Quartic.StageCertificateControl.NativePrefixState
import Proof.Wire_3_5.PrimTReadEq

/-!
# Actual whole native table execution with a retained binary header

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: the real
whole-table call, exact frame copy, bank erasure and measured retained-
frame return have a clock linear in the native budget and output bytes. -/
def nativePrefixCallCost (inputLength budget : ℕ) (payload : List Bool) : ℕ :=
  StagePrint.callAppendCost inputLength budget+5*(frame payload).length+2

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual framed native word function
is executed once on its genuine cold input bank. Its entire output is
retained unchanged, every internal tape is erased, and the actual
copied-byte counter returns the retained frame to head zero. -/
theorem nativePrefixCall_exec {Request : Type} {input payload : Request→List Bool}
    {budget : Request→ℕ} (f : WordFunction Request input (fun r => frame (payload r)) budget)
    (r : Request) (threshold cap : ℕ)
    (hcall : 2*(input r).length+2+budget r≤cap) (hcopy : (frame (payload r)).length+1≤cap) :
    let p := f.program
    ∃ τ, WXExec cap (nativePrefixCallProgram p)
      (nativePrefixLoadedState p threshold (input r)) τ
      (nativePrefixCallCost (input r).length (budget r) (payload r)) ∧
      SimW (nativePrefixReadyState p threshold (input r) (payload r)) τ := by
  let p := f.program
  let s := indexedSite p
  let σ := nativePrefixLoadedState p threshold (input r)
  have hout (i : Fin 11) : indexedExternal p i≠(indexedSite p).input :=
    (indexedBank_external_ne p (NearCubicGates.Close.WorkerArith.inTape p) i).symm
  have es (i : Fin 11) : σ.st (indexedExternal p i)=
      (if i.val=1 then frame (RepairRepresentation.natWord threshold)
       else if i.val=0 then frame (RepairRepresentation.natWord threshold++input r) else []) := by
    dsimp only [σ]
    rw [nativePrefixLoaded_eq_bank]
    simp only [WState.sets_st,Function.update_of_ne (hout i)]
    exact (nativePrefixCleared_external p threshold (input r) i).1
  have eh (i : Fin 11) : σ.sh (indexedExternal p i)=
      (if i.val=0 then 2*(RepairRepresentation.natWord threshold).length else 0) := by
    dsimp only [σ]
    rw [nativePrefixLoaded_eq_bank]
    exact (nativePrefixCleared_external p threshold (input r) i).2
  have hv (i : Fin 32) : σ.val i=
      (if i=7 then 2*(input r).length else if i=4 then 2*(RepairRepresentation.natWord threshold).length else 0) := by
    dsimp only [σ]
    rw [nativePrefixLoaded_eq_bank]
    exact nativePrefixCleared_values p threshold (input r) i
  have hT : σ.st s.tally=[] := by change σ.st (indexedExternal p 8)=[];simpa using es 8
  have hTh : σ.sh s.tally=0 := by change σ.sh (indexedExternal p 8)=0;simpa using eh 8
  have hG : σ.st s.guard=[] := by change σ.st (indexedExternal p 9)=[];simpa using es 9
  have hGh : σ.sh s.guard=0 := by change σ.sh (indexedExternal p 9)=0;simpa using eh 9
  have hL : σ.st s.ruler=[] := by change σ.st (indexedExternal p 10)=[];simpa using es 10
  have hLh : σ.sh s.ruler=0 := by change σ.sh (indexedExternal p 10)=0;simpa using eh 10
  have hdT : indexedExternal p 2≠s.tally := by
    intro h;have hh := congrArg Fin.val h;change 2=8 at hh;omega
  have hdG : indexedExternal p 2≠s.guard := by
    intro h;have hh := congrArg Fin.val h;change 2=9 at hh;omega
  have hdL : indexedExternal p 2≠s.ruler := by
    intro h;have hh := congrArg Fin.val h;change 2=10 at hh;omega
  obtain ⟨tapes,steps,τcall,hsteps,ec,hsc⟩ := StagePrint.callAppend_exec f r cap s
    (indexedExternal p 2) 14 (fun j => indexedBank_external_ne p j 2) hdT hdG
    (by change (14 : Fin 32)≠0;decide) σ
    (nativePrefixLoaded_bank p threshold (input r)).1 (nativePrefixLoaded_bank p threshold (input r)).2
    hT hTh hG hGh (by rw [hL];exact nil_blank) hLh
    (by intro i;fin_cases i <;> simp [s,indexedSite,indexedSiteRegs,hv]) hdL
    (by rw [es 2,eh 2];rfl) hcall (by rw [hv 14];simpa using hcopy)
  rw [nativePrefixCallPost_eq p threshold (input r) (payload r) tapes steps] at hsc
  let copied := nativePrefixCopiedState p threshold (input r) (payload r)
  have hc14 : copied.val (14 : Fin 32)=(frame (payload r)).length := by
    simp [copied,nativePrefixCopiedState,nativePrefixClearedState,nativePrefixReadState,appendO,startState]
  have hcHead : copied.sh (indexedExternal p 2)=(frame (payload r)).length := by
    simp [copied,nativePrefixCopiedState,nativePrefixClearedState,nativePrefixReadState,appendO,startState,indexedExternal]
  have er := wrewind_spec cap (indexedExternal p 2) (14 : Fin 32) (frame (payload r)).length copied
    hc14 (by rw [hc14];omega)
  rw [hcHead,Nat.sub_self] at er
  obtain ⟨τ,erActual,hs⟩ := wxexec_sim (WXExec.wm er) τcall hsc
  refine ⟨τ,(ec.seq erActual).mono ?_,hs⟩
  unfold nativePrefixCallCost
  omega

end NearQuarticWires.StageCertificateControl
