import Proof.Quartic.StagePrintTuple.RowHeader
import Proof.Quartic.StagePrintTuple.Request
import Proof.Quartic.StageNativeWidth.SourceFit
import Proof.Quartic.StageResize.StreamCost

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open StageTuple

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: one actual source atom names an
original occurrence and star role, with only mathematical bit/width
bounds besides the original call, header and canonical walk. -/
structure NativeKidsRequest extends RowContext where
  atom : Fin (17 * (Builder.allGates header.call).length)
  outputWidth : ℕ
  output_pos : 0 < outputWidth
  width_le : toRowContext.nativeFieldWidth ≤ outputWidth

/-- `lem:print`, paper/paper.tex: the retained
four-field binary context is independent of any Terms stream and
contains only actual original bank sizes, radix and walk ordinal. -/
def NativeKidsRequest.contextWord (r : NativeKidsRequest) : List Bool :=
  natWord r.header.call.first.gates.length ++ natWord r.header.call.second.gates.length ++
    natWord r.header.prepared.seedParameters.N ++ natWord r.walkCode.val

/-- `lem:print`, paper/paper.tex: the exact
eleven-field original-source request has five nonempty fields and
six empty fields, without a supplied gate, child, pool or count. -/
def NativeKidsRequest.sourceFields (r : NativeKidsRequest) : Fin 11 → List Bool :=
  ![frame (callWord r.header.call),
    frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord),
    r.contextWord, natWord r.atom.val, natWord r.outputWidth, [], [], [], [], [], []]

/-- `lem:print`, paper/paper.tex: one cold
native child-pool call receives only the literal original source,
actual binary metadata, actual atom and target field width. -/
def NativeKidsRequest.word (r : NativeKidsRequest) : List Bool :=
  Top.loadRec (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
    (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10)

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: the actual child count is an output
before the complete raw signed native rows, in original child order,
with one outer frame around the entire resulting word. -/
def NativeKidsRequest.output (r : NativeKidsRequest) : List Bool :=
  frame (natWord (r.toRowContext.nativeKids r.atom).length ++
    fieldsRecs r.outputWidth (r.toRowContext.nativeKids r.atom))

/-- `lem:print`, paper/paper.tex: a term-cut
caller supplies this same one-atom request without transmitting its
whole Terms stream or adding a selected-row or child-count field. -/
def NativeKidsRequest.ofTerm (r : TermCutRequest)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) : NativeKidsRequest :=
  ⟨r.toRowContext, i, r.stackWidth + 1, by omega, r.row_width_le⟩

/-- `lem:print`, paper/paper.tex: the shared
one-atom source retains the parent's exact original binary walk context. -/
theorem ofTerm_contextWord (r : TermCutRequest)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    (NativeKidsRequest.ofTerm r i).contextWord = r.contextWord := rfl

/-- `lem:print`, paper/paper.tex: the actual
signed native pool is always resized from the common physical native
header width, with no per-field source-width or value input. -/
def NativeKidsRequest.resizeRequest (r : NativeKidsRequest) : StageResize.StreamResizeRequest where
  inputWidth := r.toRowContext.nativeFieldWidth
  outputWidth := r.outputWidth
  rows := r.toRowContext.nativeKids r.atom
  input_pos := by
    unfold RowContext.nativeFieldWidth
    omega
  output_pos := r.output_pos
  width_le := r.width_le
  fits := by
    intro z hz
    obtain ⟨row, hrow, hz⟩ := List.mem_flatten.mp hz
    exact StageNativeWidth.kids_fit r.toRowContext r.atom row hrow z hz

/-- `lem:print`, paper/paper.tex: the stream
resizer consumes the actual target-width prefix, ordered native field
records and one physically emitted final delimiter. -/
theorem resizeRequest_word (r : NativeKidsRequest) :
    r.resizeRequest.word = natWord r.outputWidth ++
      fieldsRecs r.toRowContext.nativeFieldWidth (r.toRowContext.nativeKids r.atom) ++ [false] := rfl

/-- `lem:print`, paper/paper.tex: actual stream
resizing preserves every signed field and original child order in the
native child-pool reply. -/
theorem resizeRequest_output (r : NativeKidsRequest) :
    r.resizeRequest.output = fieldsRecs r.outputWidth (r.toRowContext.nativeKids r.atom) := rfl

end NearQuarticWires.StageNativeKids
