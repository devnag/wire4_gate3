import Proof.Quartic.StageTupleMonomialFinish.Stack
import Proof.Quartic.StageTupleMonomialFinish.Caches

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print`, paper/paper.tex: the original
support cache separates at the actual parsed count prefix into the
unread variable tail with its existing framing delimiter. -/
theorem support_frame {V : ℕ} (order : List (Fin V)) :
    frame (listWord natWord (order.map Fin.val))=
      marks (natWord order.length)++frame ((order.map Fin.val).flatMap natWord) := by
  simp only [listWord,List.length_map,Streaming.frame_append]

/-- `lem:print`, paper/paper.tex: after Stack,
the only changed exterior content is the literal appended cut stream
and its physically updated output-byte counter. -/
def stackState (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms) (span : ℕ) : WState (span+29) 32 :=
  appendO (data.reverseState r span data.order.length) (kernelLocal span 21) 18
    (r.stackRequest t ht).output

/-- `prop:time`, paper/paper.tex: the exact
finite caches cleaned after Stack contain only the current signed
coefficient and actual support; earlier output does not occur here. -/
def kernelCachesCost (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) : ℕ :=
  cachesCost (CoefficientRequest.word ⟨r.stackWidth+1,data.coefficient⟩)
    (frame (SignedSortKey.binary (r.stackWidth+1)
      (NearCubicGates.Close.WordPrograms.SInt.encS data.coefficient)))
    (marks (natWord data.order.length)) ((data.order.map Fin.val).flatMap natWord)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual post-Stack state satisfies every physical
finite-cache cleanup condition, including the measured full support
length and its current post-count source cursor. -/
theorem kernelCaches_spec (span cap : ℕ) (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ) (ht : t∈r.terms)
    (hc : ((data.reverseData r data.order.length).caches 1).length≤cap)
    (hr : ((data.reverseData r data.order.length).caches 2).length≤cap)
    (hs : ((data.reverseData r data.order.length).caches 0).length≤cap) :
    ∃τ,WXExec cap (cachesProgram span) (stackState r data t ht span) τ
      (kernelCachesCost r data) ∧
      SimW (cachesState span (stackState r data t ht span)) τ := by
  apply cachesProgram_spec span cap
    (CoefficientRequest.word ⟨r.stackWidth+1,data.coefficient⟩)
    (frame (SignedSortKey.binary (r.stackWidth+1)
      (NearCubicGates.Close.WordPrograms.SInt.encS data.coefficient)))
    (marks (natWord data.order.length)) ((data.order.map Fin.val).flatMap natWord)
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal,CoefficientRequest.output]
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal,support_frame]
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · simp [stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · simp [stackState,appendO,MonomialData.reverseState,KernelData.state]
  · simp [stackState,appendO,MonomialData.reverseState,KernelData.state]
  · simp [stackState,appendO,MonomialData.reverseState,support_frame]
  · exact hc
  · exact hr
  · change (frame (listWord natWord (data.order.map Fin.val))).length≤cap at hs
    simpa only [←support_frame] using hs

end NearQuarticWires.StageTupleMonomialFinish
