import Proof.Quartic.StagePrintTuple.KernelMaps
import Proof.Quartic.StagePrintTuple.HistoryClose

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print`, paper/paper.tex: actual counted
clears reset the processed stride, tuple census and support cardinal,
leaving all source, remaining-term and output counters unchanged. -/
def clearCounts {ns : ℕ} : WM ns 32 :=
  .seq (WM.clear 12) (.seq (WM.clear 14) (WM.clear 16))

/-- `prop:time`, paper/paper.tex: clearing the
three true local counters costs their sum and never depends on the
numeric magnitude of a signed coefficient. -/
theorem clearCounts_spec {ns : ℕ} (cap : ℕ) (σ : WState ns 32)
    (h12 : σ.val 12≤cap) (h14 : σ.val 14≤cap) (h16 : σ.val 16≤cap) :
    WExec cap clearCounts σ (((σ.setv 12 0).setv 14 0).setv 16 0)
      (100*(σ.val 12+σ.val 14+σ.val 16+1)) := by
  have e1 := wclear_spec cap 12 (σ.val 12) σ rfl h12
  have e2 := wclear_spec cap 14 (σ.val 14) (σ.setv 12 0) (by simp) (by simpa using h14)
  have e3 := wclear_spec cap 16 (σ.val 16) ((σ.setv 12 0).setv 14 0)
    (by simp) (by simpa using h16)
  exact (e1.seq (e2.seq e3)).mono (by omega)

/-- `lem:print`, paper/paper.tex: only the
current tuple segment is traversed before one real empty-tuple
delimiter is appended and selected by its measured one-cell rewind. -/
def nextHistory (span : ℕ) : WM (span+29) 32 :=
  .seq (advanceRecordHistory (kernelLocal span 20) 1)
    (closeRecordHistory (kernelLocal span 20) 0)

/-- `lem:print`, paper/paper.tex: all previous
history remains literal, and the final appended false cell is the
next empty-tuple segment. -/
def nextHistoryState (span : ℕ) (σ : WState (span+29) 32) : WState (span+29) 32 :=
  ((σ.sets (kernelLocal span 20) (σ.st (kernelLocal span 20)++[false])).seth
    (kernelLocal span 20) (σ.st (kernelLocal span 20)).length).setv 0 0

/-- `lem:print` and `prop:time`, paper/paper.tex: history advancement scans precisely the current records
and charges the genuine delimiter write and rewind, independently of
the retained earlier history prefix. -/
theorem nextHistory_spec (span cap : ℕ) (pre : List Bool) (records : List (List Bool))
    (hne : ∀record∈records,record≠[]) (σ : WState (span+29) 32)
    (hs : σ.st (kernelLocal span 20)=pre++records.flatMap frame++[false])
    (hh : σ.sh (kernelLocal span 20)=pre.length)
    (hg : σ.st (kernelLocal span 28)=[]) (hgh : σ.sh (kernelLocal span 28)=0)
    (h0 : σ.val 0=0) (h1 : σ.val 1=0)
    (hcap : (records.flatMap frame).length+1≤cap) :
    WExec cap (nextHistory span) σ (nextHistoryState span σ)
      (100*((records.flatMap frame).length+1)) := by
  have e1 := advanceRecordHistory_spec cap (kernelLocal span 20) (kernelLocal span 28) 1 0
    ((kernelLocal span).injective.ne (by decide)) (by decide) records pre hne σ hs hh
    (by simp [hg,hgh]) (by rw [h0];omega) h1 (by omega)
  let a := σ.seth (kernelLocal span 20) (σ.st (kernelLocal span 20)).length
  have e2 := closeRecordHistory_spec cap (kernelLocal span 20) 0
    (σ.st (kernelLocal span 20)) [] a (by simp [a]) (by simp [a])
    (by simp [a,h0]) (by simp only [List.length_nil];omega)
  refine (e1.seq e2).cast cap ?_ (by simp only [List.length_nil];omega)
  apply WState.eq
  · funext i
    by_cases hi:i=kernelLocal span 20
    · subst i;simp [a,closedHistory,nextHistoryState]
    · simp [a,closedHistory,nextHistoryState,Function.update_of_ne hi]
  · simp [a,closedHistory,nextHistoryState]
  · rfl
  · rfl

end NearQuarticWires.StageTupleMonomialFinish
