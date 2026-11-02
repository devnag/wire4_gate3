import Proof.Quartic.StagePrintTuple.NativePhaseContract
import Proof.Quartic.StagePrintTuple.NativeCleanup
import Proof.Quartic.StagePrintTuple.HistoryClose

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: actual native
reply and selected-atom caches cancel from the reusable boundary after
their measured erasure. Only the new history and real tuple counters
remain; the genuine reply bytes are not retained as another premise. -/
theorem nativeTransition_normalize (span : ℕ) (r : StageNativeKids.NativeKidsRequest)
    (σ : WState (span+29) 32) (atom records : List Bool) (K N : ℕ)
    (h17 : σ.st (kernelLocal span 17)=[])
    (h18 : σ.st (kernelLocal span 18)=[])
    (h19 : σ.st (kernelLocal span 19)=[])
    (hh18 : σ.sh (kernelLocal span 18)=0)
    (hh19 : σ.sh (kernelLocal span 19)=0)
    (h24 : σ.val 24=0) (h25 : σ.val 25=0) :
    nativeCleanupState span
      ((((closedHistory (nativePhaseState span r (σ.sets (kernelLocal span 17) (frame atom)))
        (kernelLocal span 20) 0 (σ.st (kernelLocal span 20)) records).setv
          14 (K*σ.val 14)).setv 13 0).setv 12 (σ.val 12+N))=
    (((closedHistory σ (kernelLocal span 20) 0 (σ.st (kernelLocal span 20)) records).setv
      14 (K*σ.val 14)).setv 13 0).setv 12 (σ.val 12+N) := by
  have kl {i j : Fin 30} : kernelLocal span i=kernelLocal span j ↔ i=j :=
    (kernelLocal span).injective.eq_iff
  apply WState.eq
  · funext i
    by_cases hi18:i=kernelLocal span 18
    · subst i;simp [nativeCleanupState,nativePhaseState,closedHistory,kl,hh18]
    · by_cases hi19:i=kernelLocal span 19
      · subst i;simp [nativeCleanupState,nativePhaseState,closedHistory,kl,hh19]
      · by_cases hi20:i=kernelLocal span 20
        · subst i;simp [nativeCleanupState,nativePhaseState,closedHistory,kl]
        · simp [nativeCleanupState,nativePhaseState,closedHistory,
            Function.update_of_ne hi18,Function.update_of_ne hi19,Function.update_of_ne hi20]
  · funext i
    by_cases hi17:i=kernelLocal span 17
    · subst i;simp [nativeCleanupState,nativePhaseState,closedHistory,kl,h17]
    · by_cases hi18:i=kernelLocal span 18
      · subst i;simp [nativeCleanupState,nativePhaseState,closedHistory,kl,h18]
      · by_cases hi19:i=kernelLocal span 19
        · subst i;simp [nativeCleanupState,nativePhaseState,closedHistory,kl,h19]
        · by_cases hi20:i=kernelLocal span 20
          · subst i;simp [nativeCleanupState,nativePhaseState,closedHistory,kl]
          · simp [nativeCleanupState,nativePhaseState,closedHistory,
              Function.update_of_ne hi17,Function.update_of_ne hi18,Function.update_of_ne hi19,
              Function.update_of_ne hi20]
  · funext i
    fin_cases i <;> simp [nativeCleanupState,nativePhaseState,closedHistory,h24,h25]
  · rfl

end NearQuarticWires.StageTuple
