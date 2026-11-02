import Proof.Quartic.StagePrint.CallAppend

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

variable {ns nr : ℕ} {p : Program}

/-- `lem:print`, paper/paper.tex: cleanup removes all data of the preceding child call and preserves its original exterior state. -/
theorem cleanState_called (s : Site p ns nr) (σ : WState ns nr)
    (tapes : Fin p.tapeCount→List Bool) (w steps : ℕ) :
    cleanState s (calledState s σ tapes w steps)=cleanState s σ := by
  apply WState.eq
  · funext i
    by_cases hb : ∃j,s.bank j=i
    · obtain ⟨j,rfl⟩:=hb
      simp [cleanState,calledState,updS,NearCubicWires.ExtDecompositionBatch.dockH_slot,s.bank_inj]
    · have hp : RecoveryFocus.pick s.bank i=none := by simp [RecoveryFocus.pick,hb]
      simp [cleanState,calledState,updS,NearCubicWires.ExtDecompositionBatch.dockH,hp]
  · funext i
    by_cases hb : ∃j,s.bank j=i
    · obtain ⟨j,rfl⟩:=hb
      simp [cleanState,calledState,updS,install,s.bank_inj,RecoveryFocus.pick_slot,
        s.guard_ne j,s.tally_ne j]
    · have hp : RecoveryFocus.pick s.bank i=none := by simp [RecoveryFocus.pick,hb]
      by_cases hg : i=s.guard <;> by_cases ht : i=s.tally <;>
        simp [cleanState,calledState,updS,install,hp,Function.update_apply,hg,ht]
  · rfl
  · rfl

/-- `lem:print`, paper/paper.tex: child-bank cleanup commutes with appending records outside the bank. -/
theorem cleanState_append (s : Site p ns nr) (σ : WState ns nr)
    (dst : Fin (ns+1)) (OP : Fin nr) (bits : List Bool)
    (hdB : ∀j,s.bank j≠dst) (hdT : dst≠s.tally) (hdG : dst≠s.guard) :
    cleanState s (appendO σ dst OP bits)=appendO (cleanState s σ) dst OP bits := by
  have hpD : RecoveryFocus.pick s.bank dst=none := by
    simp [RecoveryFocus.pick,show ¬∃j,s.bank j=dst by simpa using hdB]
  apply WState.eq
  · funext i
    by_cases hi : i=dst
    · subst hi
      simp [cleanState,appendO,updS,NearCubicWires.ExtDecompositionBatch.dockH,hpD]
    · by_cases hb : ∃j,s.bank j=i
      · obtain ⟨j,rfl⟩:=hb
        simp [cleanState,appendO,updS,NearCubicWires.ExtDecompositionBatch.dockH_slot,s.bank_inj,hdB j]
      · have hp : RecoveryFocus.pick s.bank i=none := by simp [RecoveryFocus.pick,hb]
        simp [cleanState,appendO,updS,NearCubicWires.ExtDecompositionBatch.dockH,hp,hi]
  · funext i
    by_cases hi : i=dst
    · subst hi
      simp [cleanState,appendO,updS,install,hpD,hdT,hdG]
    · by_cases hb : ∃j,s.bank j=i
      · obtain ⟨j,rfl⟩:=hb
        simp [cleanState,appendO,updS,install,RecoveryFocus.pick_slot,s.bank_inj,hdB j,
          s.guard_ne j,s.tally_ne j]
      · have hp : RecoveryFocus.pick s.bank i=none := by simp [RecoveryFocus.pick,hb]
        simp [cleanState,appendO,updS,install,hp,hi,Function.update_apply]
  · rfl
  · rfl

/-- `lem:print`, paper/paper.tex: the exact copied pool state is independent of every erased child computation. -/
theorem callAppendPost_eq (s : Site p ns nr) (σ : WState ns nr)
    (tapes : Fin p.tapeCount→List Bool) (w steps : ℕ)
    (dst : Fin (ns+1)) (OP : Fin nr) (bits : List Bool)
    (hdB : ∀j,s.bank j≠dst) (hdT : dst≠s.tally) (hdG : dst≠s.guard) :
    cleanState s (appendO (calledState s σ tapes w steps) dst OP bits)=
      appendO (cleanState s σ) dst OP bits := by
  rw [cleanState_append s _ dst OP bits hdB hdT hdG,cleanState_called]

/-- `lem:print`, paper/paper.tex: cleanup restores an already empty reusable call bank exactly. -/
theorem cleanState_self (s : Site p ns nr) (σ : WState ns nr)
    (hb : ∀j,σ.st (s.bank j)=[]) (hh : ∀j,σ.sh (s.bank j)=0)
    (ht : σ.st s.tally=[]) (hg : σ.st s.guard=[]) : cleanState s σ=σ := by
  apply WState.eq
  · funext i
    by_cases hbi : ∃j,s.bank j=i
    · obtain ⟨j,rfl⟩:=hbi
      simp [cleanState,updS,dockH_slot,s.bank_inj,hh]
    · have hp : RecoveryFocus.pick s.bank i=none := by simp [RecoveryFocus.pick,hbi]
      simp [cleanState,updS,dockH,hp]
  · funext i
    by_cases hiG : i=s.guard
    · subst hiG;simp [cleanState,hg]
    · by_cases hiT : i=s.tally
      · subst hiT;simp [cleanState,hiG,ht]
      · by_cases hbi : ∃j,s.bank j=i
        · obtain ⟨j,rfl⟩:=hbi
          simp [cleanState,updS,install,RecoveryFocus.pick_slot,s.bank_inj,hb,s.guard_ne j,s.tally_ne j]
        · have hp : RecoveryFocus.pick s.bank i=none := by simp [RecoveryFocus.pick,hbi]
          simp [cleanState,updS,install,hp,hiG,hiT]
  · rfl
  · rfl

/-- `lem:print`, paper/paper.tex: the next input word is erased with its work bank before another occurrence is processed. -/
theorem cleanState_set_bank (s : Site p ns nr) (σ : WState ns nr) (j : Fin p.tapeCount)
    (bits : List Bool) : cleanState s (σ.sets (s.bank j) bits)=cleanState s σ := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hbi : ∃k,s.bank k=i
    · obtain ⟨k,rfl⟩:=hbi
      simp [cleanState,updS,install,RecoveryFocus.pick_slot,s.bank_inj,s.guard_ne k,s.tally_ne k]
    · have hp : RecoveryFocus.pick s.bank i=none := by simp [RecoveryFocus.pick,hbi]
      have hi : i≠s.bank j := by rintro rfl;exact hbi ⟨j,rfl⟩
      simp [cleanState,updS,install,hp,Function.update_of_ne hi,Function.update_apply]
  · rfl
  · rfl

end NearQuarticWires.StagePrint
