import Proof.Quartic.StageTupleMonomialFinish.KernelCaches
import Proof.Quartic.StageTupleMonomialFinish.Reset

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print`, paper/paper.tex: after finite
cache erasure, all local counts are physically cleared and a new empty
tuple segment is appended at the real end of the current history. -/
def resetProgram (span : ℕ) : WMX (span+29) 32 :=
  .seq (.wm clearCounts) (.wm (nextHistory span))

/-- `lem:print`, paper/paper.tex: the final
history reset changes no retained source or signed-cut output data. -/
def resetState (span : ℕ) (σ : WState (span+29) 32) : WState (span+29) 32 :=
  nextHistoryState span (((σ.setv 12 0).setv 14 0).setv 16 0)

/-- `prop:time`, paper/paper.tex: the remaining
local counts and current tuple bytes pay all reset operations; no
previous tuple segment contributes to this cost. -/
def resetCost (sr : StagePrint.StackRequest) : ℕ :=
  100*(sr.m*(sr.s+1)+sr.tuples.length+sr.m+1)+1+
    100*(((fieldRecords (sr.W+1) (sr.tuples.map List.flatten)).flatMap frame).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact actual monomial state satisfies the counted
reset and current-segment scan contracts, including empty supports. -/
theorem kernelReset_spec (span cap : ℕ) (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ) (ht : t∈r.terms)
    (horder : data.order=t.1.sort (·≤·))
    (hcount : (r.stackRequest t ht).m*((r.stackRequest t ht).s+1)+
      (r.stackRequest t ht).tuples.length+(r.stackRequest t ht).m≤cap)
    (hfields : ((fieldRecords ((r.stackRequest t ht).W+1)
      ((r.stackRequest t ht).tuples.map List.flatten)).flatMap frame).length+1≤cap) :
    WXExec cap (resetProgram span) (cachesState span (stackState r data t ht span))
      (resetState span (cachesState span (stackState r data t ht span)))
      (resetCost (r.stackRequest t ht)) := by
  let a := cachesState span (stackState r data t ht span)
  let sr := r.stackRequest t ht
  have h12 : a.val 12=sr.m*(sr.s+1) := by
    simp [a,cachesState,stackState,appendO,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state,sr,TermCutRequest.stackRequest,horder]
  have h14 : a.val 14=sr.tuples.length := by
    simp [a,cachesState,stackState,appendO,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state,sr,TermCutRequest.stackRequest,horder,
      processedSupport,tupleFields,TermCutRequest.monomialTuples]
  have h16 : a.val 16=sr.m := by
    simp [a,cachesState,stackState,appendO,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state,sr,TermCutRequest.stackRequest,horder]
  dsimp only [sr] at h12 h14 h16
  have e1 := clearCounts_spec cap a (by rw [h12];omega) (by rw [h14];omega) (by rw [h16];omega)
  let b := ((a.setv 12 0).setv 14 0).setv 16 0
  have kl {i j : Fin 30} : kernelLocal span i=kernelLocal span j ↔ i=j :=
    (kernelLocal span).injective.eq_iff
  have e2 := nextHistory_spec span cap (finalHistoryPrefix r data)
    (fieldRecords (sr.W+1) (sr.tuples.map List.flatten))
    (fieldRecords_nonempty _ (by omega) _) b
    (by simpa [b,a,cachesState,stackState,appendO,kl] using
      complete_history r data t ht horder span)
    (by simpa [b,a,cachesState,stackState,appendO,kl] using
      complete_history_head r data span)
    (by simp [b,a,cachesState,stackState,appendO,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state,kernelLocal])
    (by simp [b,a,cachesState,stackState,appendO,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state,kernelLocal])
    (by simp [b,a,cachesState,stackState,appendO,MonomialData.reverseState,KernelData.state])
    (by simp [b,a,cachesState,stackState,appendO,MonomialData.reverseState,KernelData.state]) hfields
  exact ((WXExec.wm e1).seq (WXExec.wm e2)).mono
    (by simp only [resetCost,h12,h14,h16,sr];omega)

end NearQuarticWires.StageTupleMonomialFinish
