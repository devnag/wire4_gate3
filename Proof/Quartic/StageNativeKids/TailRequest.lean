import Proof.Quartic.StageNativeKids.Request

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- `lem:print`, paper/paper.tex: the
internal finalizer receives the actual computed child-count codec and
the concrete ordered native resize source, with no additional oracle. -/
structure ResizeTailRequest where
  stream : StageResize.StreamResizeRequest

/-- `lem:print`, paper/paper.tex: the
actual computed child count precedes the unchanged target-width and
raw native-record stream, including its real final delimiter. -/
def ResizeTailRequest.word (r : ResizeTailRequest) : List Bool :=
  natWord r.stream.rows.length ++ r.stream.word

/-- `lem:print`, paper/paper.tex: the
finalizer retains the literal count codec, resizes every actual field
once and writes one outer frame around the complete native reply. -/
def ResizeTailRequest.output (r : ResizeTailRequest) : List Bool :=
  frame (natWord r.stream.rows.length ++ r.stream.output)

/-- `prop:time`, paper/paper.tex: a fixed
quadratic source clock pays finite count-codec copying, one concrete
stream-resize computation and all output framing and tape returns. -/
noncomputable def ResizeTailRequest.budget (r : ResizeTailRequest) : ℕ :=
  100000000 * (r.word.length + r.stream.budget + 1) ^ 2

/-- `lem:print`, paper/paper.tex: the
actual native pool supplies the unchanged finalizer request after its
original compiler count and ordered original-row loop are computed. -/
def NativeKidsRequest.resizeTailRequest (r : NativeKidsRequest) : ResizeTailRequest :=
  ⟨r.resizeRequest⟩

/-- `lem:print`, paper/paper.tex: the
internal finalizer output is exactly the original native-pool reply,
without changing the parent's eleven-field caller word. -/
theorem resizeTailRequest_output (r : NativeKidsRequest) :
    r.resizeTailRequest.output = r.output := rfl

/-- `lem:print`, paper/paper.tex: the
actual native row loop supplies the computed count, width codec,
ordered raw original-row fields and final physical stream delimiter. -/
theorem resizeTailRequest_word (r : NativeKidsRequest) :
    r.resizeTailRequest.word = natWord (r.toRowContext.nativeKids r.atom).length ++
      natWord r.outputWidth ++ NearCubicGates.Close.TabMachine.fieldsRecs
        r.toRowContext.nativeFieldWidth (r.toRowContext.nativeKids r.atom) ++ [false] := by
  simp only [NativeKidsRequest.resizeTailRequest, ResizeTailRequest.word,
    NativeKidsRequest.resizeRequest, StageResize.StreamResizeRequest.word, List.append_assoc]

end NearQuarticWires.StageNativeKids
