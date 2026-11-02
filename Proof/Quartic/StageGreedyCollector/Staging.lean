import Proof.Quartic.StageGreedyCollector.StagePrefix

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open Reconstruct.Batch (appendT)

/-- `lem:print`, paper/paper.tex: one common
header and one finite context precede the actual original ordered entries. -/
structure StagingRequest where
  header : List Bool
  context : List Bool
  count : ℕ
  entries : List Entry

def StagingRequest.word (r : StagingRequest) : List Bool :=
  frame r.header++frame r.context++natWord r.count++r.entries.flatMap Entry.word

def StagingRequest.batch (r : StagingRequest) : BatchSource :=
  ⟨r.header,r.count,r.entries.map (fun entry=>r.context++entry.word)⟩

def StagingRequest.capacity (r : StagingRequest) : ℕ :=
  2*(r.word.length+r.context.length+1)+10

def StagingRequest.steps (r : StagingRequest) : ℕ :=
  400*(r.word.length+r.entries.length*(r.context.length+1)+1)

/-- `lem:print`, paper/paper.tex: the
finite program loads the source once, stores its small context, then
copies each original indexed request with its reply tag. -/
def stagingProgram : WMX 3 3 :=
  .seq (.wm (StageGamma.unframeRecord 0 1 0))
    (.seq (.wm stagePrefix) (.wm (.whs 1 (taggedEntry 1 2 3 0 1 2))))

/-- `lem:print` and `prop:time`, paper/paper.tex: all actual entries are staged by a single streaming
pass, with linear total byte cost and the repeated finite context charged. -/
theorem stagingProgram_run (r : StagingRequest) :
    ∃ b, WXExec r.capacity stagingProgram (idealStart 3 3 r.word (fun _=>0)) b r.steps ∧
      b.st 3=r.batch.word := by
  let a:=idealStart 3 3 r.word (fun _=>0)
  let b:=(a.sets 1 r.word).seth 0 (2*r.word.length+1)
  have e1 : WExec r.capacity (StageGamma.unframeRecord 0 1 0) a b (23*r.word.length+5) := by
    simpa [a,b,idealStart] using
      StageGamma.unframeRecord_run r.capacity (0 : Fin 4) 1 (by decide) (0 : Fin 3)
        r.word [] [] a (by simp [a,idealStart]) rfl rfl rfl
        (by unfold StagingRequest.capacity;omega)
  have e2:=stagePrefix_spec r.capacity r.header r.context (r.entries.flatMap Entry.word) r.count b
    rfl rfl rfl rfl rfl rfl rfl (by
      unfold StagingRequest.capacity StagingRequest.word
      simp only [List.length_append]
      omega)
  let c:=stagePrefixState b r.header r.context r.count
  let pre:=frame r.header++frame r.context++natWord r.count
  have hsrc : c.st 1=pre++r.entries.flatMap Entry.word := by
    simp [c,b,stagePrefixState,pre,StagingRequest.word]
  have e3:=prepareTaggedEntries_spec r.capacity (1 : Fin 4) 2 3 (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r.context r.entries pre c hsrc
    (by simp [c,stagePrefixState,pre,List.length_append];omega)
    (by simp [c,stagePrefixState])
    (by simp [c,b,stagePrefixState,a,idealStart])
    (by simp [c,stagePrefixState,List.length_append]) rfl rfl rfl (by
      unfold StagingRequest.capacity StagingRequest.word
      simp only [List.length_append]
      omega)
  refine ⟨_,(WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))).mono ?_,?_⟩
  · unfold StagingRequest.steps StagingRequest.word
    simp only [List.length_append]
    omega
  · simp [appendT,c,stagePrefixState,StagingRequest.batch,BatchSource.word,batchSource,
      requestPairs,taggedRequests,List.flatMap_map,List.append_assoc]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual raw batch is the result of one uniform
ordinary machine, with no parsed-entry or decoded-count premise. -/
noncomputable def stagingRawWordFunction :
    WordFunction StagingRequest StagingRequest.word (fun r=>r.batch.word) (fun r=>2*r.steps+2) :=
  wordFunction_of_ideal stagingProgram 3 (by decide) StagingRequest.capacity (fun _ _=>0)
    StagingRequest.steps (fun _=>le_rfl) (by intro r;exact ⟨rfl,stagingProgram_run r⟩)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual batch is physically framed for the
next ordinary call, including every byte, marker and reset. -/
noncomputable def stagingWordFunction :
    WordFunction StagingRequest StagingRequest.word (fun r=>frame r.batch.word)
      (fun r=>2*frameAfterCost (source:=StagingRequest.batch) (budget:=fun r=>2*r.steps+2) r+2) :=
  frameAfterWordFunction stagingRawWordFunction

end NearQuarticWires.StageGreedyCollector
