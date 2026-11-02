import Proof.Quartic.StageGreedyCollector.FirstPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open Reconstruct.Batch (appendT)

/-- `lem:print`, paper/paper.tex: the first
original entry follows the finite context and one binary count; every
remaining source byte is retained as an arbitrary unread suffix. -/
structure FirstRequest where
  context : List Bool
  count : ℕ
  entry : Entry
  suffix : List Bool

def FirstRequest.word (r : FirstRequest) : List Bool :=
  frame r.context++natWord r.count++r.entry.word++r.suffix

def FirstRequest.output (r : FirstRequest) : List Bool :=frame (r.context++r.entry.word)

def FirstRequest.capacity (r : FirstRequest) : ℕ :=2*(r.word.length+r.context.length+1)+10

def FirstRequest.steps (r : FirstRequest) : ℕ :=400*(r.word.length+r.context.length+r.entry.word.length+1)

/-- `lem:print`, paper/paper.tex: the
first-entry extractor reads real source bits, stores its finite context,
and emits the actual first indexed Terms request once. -/
def firstEntryProgram : WMX 4 3 :=
  .seq (.wm (StageGamma.unframeRecord 0 1 0))
    (.seq (.wm firstPrefix) (.wm (prepareEntry 1 2 3 0 1 2)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the once-only header request is extracted by
physical transitions; the input count and index remain binary throughout. -/
theorem firstEntryProgram_run (r : FirstRequest) :
    ∃ b, WXExec r.capacity firstEntryProgram (idealStart 4 3 r.word (fun _=>0)) b r.steps ∧
      b.st 3=r.output := by
  let a:=idealStart 4 3 r.word (fun _=>0)
  let b:=(a.sets 1 r.word).seth 0 (2*r.word.length+1)
  have e1 : WExec r.capacity (StageGamma.unframeRecord 0 1 0) a b (23*r.word.length+5) := by
    simpa [a,b,idealStart] using
      StageGamma.unframeRecord_run r.capacity (0 : Fin 5) 1 (by decide) (0 : Fin 3)
        r.word [] [] a (by simp [a,idealStart]) rfl rfl rfl
        (by unfold FirstRequest.capacity;omega)
  have e2:=firstPrefix_spec r.capacity r.context (r.entry.word++r.suffix) r.count b
    (by simp [b,FirstRequest.word,List.append_assoc]) rfl rfl rfl rfl rfl rfl (by
      unfold FirstRequest.capacity FirstRequest.word
      simp only [List.length_append];omega)
  let c:=firstPrefixState b r.context r.count
  let pre:=frame r.context++natWord r.count
  have hsrc : c.st 1=pre++r.entry.word++r.suffix := by
    simp [c,b,firstPrefixState,pre,FirstRequest.word]
  have e3:=prepareEntry_spec r.capacity (1 : Fin 5) 2 3 (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (by decide) (by decide)
    r.context r.entry pre r.suffix c hsrc
    (by simp [c,firstPrefixState,pre,List.length_append])
    (by simp [c,firstPrefixState])
    (by simp [c,b,firstPrefixState,a,idealStart])
    (by simp [c,b,firstPrefixState,a,idealStart]) rfl rfl rfl (by
      unfold FirstRequest.capacity FirstRequest.word
      simp only [List.length_append];omega)
  refine ⟨_,(WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))).mono ?_,?_⟩
  · unfold FirstRequest.steps FirstRequest.word
    simp only [List.length_append]
    omega
  · simp [appendT,c,b,firstPrefixState,a,idealStart,FirstRequest.output]

/-- `lem:print` and `prop:time`, paper/paper.tex: one uniform ordinary extractor supplies the actual
first entry to the header computation, paying the one source acquisition. -/
noncomputable def firstEntryWordFunction :
    WordFunction FirstRequest FirstRequest.word FirstRequest.output (fun r=>2*r.steps+2) :=
  wordFunction_of_ideal firstEntryProgram 3 (by decide) FirstRequest.capacity (fun _ _=>0)
    FirstRequest.steps (fun _=>le_rfl) (by intro r;exact ⟨rfl,firstEntryProgram_run r⟩)

end NearQuarticWires.StageGreedyCollector
