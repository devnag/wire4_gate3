import Proof.Quartic.StageCertificateControl.CountBank

/-!
# Exact pool state after count-bank cleanup

Paper: `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: the count
call receives a physical copy while the original source stays untouched. -/
noncomputable def countLoadedState (p q : Program) (hq : q.tapeCount≤p.tapeCount)
    (source : List Bool) : WState (p.tapeCount+5) 16 :=
  (startState (p.tapeCount+5) 16 source).sets (countBankSite p q hq).input (frame source)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: cleanup leaves exactly the initial native-pool
state, including blank unused bank tapes and the actual count register. -/
theorem countCleared_state (p q : Program) (hq : q.tapeCount≤p.tapeCount)
    (source : List Bool) (cache : ℕ→List Bool) (T steps : ℕ)
    (tapes : Fin q.tapeCount→List Bool) :
    cleanState (countBankSite p q hq)
      ((calledState (countBankSite p q hq) (countLoadedState p q hq source)
        tapes source.length steps).setv 14 T)=StagePrint.poolState p source cache 0 T := by
  classical
  let s := countBankSite p q hq
  let a := countLoadedState p q hq source
  have hbank0 (j : Fin q.tapeCount) : (s.bank j).val≠0 := by change 5+j.val≠0;omega
  have hbank1 (j : Fin q.tapeCount) : (s.bank j).val≠1 := by change 5+j.val≠1;omega
  apply WState.eq
  · funext i
    by_cases hb : ∃j,s.bank j=i
    · obtain ⟨j,rfl⟩ := hb
      change (updS s.bank _ (fun _ => 0) (fun _ => [])).sh (s.bank j)=_
      rw [updS_sh_slot s.bank _ _ _ s.bank_inj]
      simp [StagePrint.poolState,StagePrint.poolPrefix]
    · have hn : ∀j,s.bank j≠i := fun j hj => hb ⟨j,hj⟩
      change (updS s.bank _ (fun _ => 0) (fun _ => [])).sh i=_
      rw [updS_sh_other s.bank _ _ _ i hn]
      change (updS s.bank a (fun _ => 0) tapes).sh i=_
      rw [updS_sh_other s.bank _ _ _ i hn]
      simp [a,countLoadedState,startState,StagePrint.poolState,StagePrint.poolPrefix]
  · funext i
    by_cases hG : i=s.guard
    · subst i
      simp [s,cleanState,countBankSite,StagePrint.poolState,StagePrint.poolPrefix]
    · by_cases hT : i=s.tally
      · subst i
        simp [s,cleanState,countBankSite,StagePrint.poolState,StagePrint.poolPrefix]
      · by_cases hb : ∃j,s.bank j=i
        · obtain ⟨j,rfl⟩ := hb
          change (((updS s.bank _ (fun _ => 0) (fun _ => [])).sets s.tally []).sets s.guard []).st (s.bank j)=_
          simp only [WState.sets_st,Function.update_of_ne (s.guard_ne j),Function.update_of_ne (s.tally_ne j)]
          rw [updS_st_slot s.bank _ _ _ s.bank_inj]
          have hj0 : s.bank j≠(0 : Fin (p.tapeCount+6)) := by
            intro h;exact hbank0 j (congrArg Fin.val h)
          simp [StagePrint.poolState,StagePrint.poolPrefix,hbank0,hbank1,hj0]
        · have hn : ∀j,s.bank j≠i := fun j hj => hb ⟨j,hj⟩
          have hi : i≠s.input := by intro h;apply hb;exact ⟨inTape q,h.symm⟩
          have hi' : i≠(countBankSite p q hq).input := hi
          change (((updS s.bank _ (fun _ => 0) (fun _ => [])).sets s.tally []).sets s.guard []).st i=_
          simp only [WState.sets_st,Function.update_of_ne hG,Function.update_of_ne hT]
          rw [updS_st_other s.bank _ _ _ i hn]
          change (((updS s.bank a (fun _ => 0) tapes).sets s.tally _).sets s.guard _).st i=_
          simp only [WState.sets_st,Function.update_of_ne hG,Function.update_of_ne hT]
          rw [updS_st_other s.bank _ _ _ i hn]
          simp [a,countLoadedState,Function.update_of_ne hi',startState,
            StagePrint.poolState,StagePrint.poolPrefix]
  · funext i
    fin_cases i <;> rfl
  · rfl

end NearQuarticWires.StageCertificateControl
