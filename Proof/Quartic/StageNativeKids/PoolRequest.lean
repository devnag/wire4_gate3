import Proof.Quartic.StageNativeKids.SelectSource
import Proof.Quartic.StageNativeKids.CounterMachine
import Proof.Quartic.StageNativeKids.TailRequest
import Proof.Quartic.StageMain.TaggedWordFunction

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `lem:print`, paper/paper.tex: the
internal original-pool source has only the real indexed original call,
actual affine header and target-width codec, with no child count or row
list as an input field. -/
def poolSourceWord (source header : List Bool) (width : ℕ) : List Bool :=
  Top.loadRec (frame source) (frame header) (natWord width) [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the
first-bank child-pool machine reads its actual original occurrence and
affine metadata after the real bank selector has constructed them. -/
def firstPoolWord (r : FirstBankRequest) : List Bool :=
  poolSourceWord (natWord (r.val.toRowContext.originalIndex r.val.atom).val ++ callWord r.val.header.call)
    (r.val.toRowContext.rowHeader r.val.atom) r.val.outputWidth

/-- `lem:print`, paper/paper.tex: the
second-bank pool reads the exact physically normalized occurrence index
and the same original call bytes, header and target width. -/
def secondPoolWord (r : SecondBankRequest) : List Bool :=
  poolSourceWord (natWord ((r.val.toRowContext.originalIndex r.val.atom).val -
    r.val.header.call.first.gates.length) ++ callWord r.val.header.call)
    (r.val.toRowContext.rowHeader r.val.atom) r.val.outputWidth

/-- `lem:print`, paper/paper.tex: the
actual original occurrence determines the branch of the concrete two-bank
ordinary selector, including equality and empty first banks. -/
def actualBankRequest (r : NativeKidsRequest) : FirstBankRequest ⊕ SecondBankRequest :=
  if h : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val
  then .inr ⟨r, h⟩ else .inl ⟨r, by omega⟩

/-- `lem:print`, paper/paper.tex: the
actual branch bit precedes the exact three-field internal pool source;
the parent's original eleven-field caller interface is unchanged. -/
def NativeKidsRequest.bankWord (r : NativeKidsRequest) : List Bool :=
  decide (r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val) ::
    poolSourceWord (selectedSourceWord r.header.call.first.gates.length
      (r.toRowContext.originalIndex r.atom).val (callWord r.header.call))
      (r.toRowContext.rowHeader r.atom) r.outputWidth

/-- `lem:print`, paper/paper.tex: the
physical computed bank bit and source bytes are exactly the existing
ordinary two-bank selector's tagged input for the actual original atom. -/
theorem actualBankRequest_word (r : NativeKidsRequest) :
    StageMain.Tagged.taggedInput firstPoolWord secondPoolWord (actualBankRequest r) = r.bankWord := by
  by_cases h : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val
  · simp [actualBankRequest, StageMain.Tagged.taggedInput,
      secondPoolWord, NativeKidsRequest.bankWord, selectedSourceWord,
      h]
  · simp [actualBankRequest, StageMain.Tagged.taggedInput,
      firstPoolWord, NativeKidsRequest.bankWord, selectedSourceWord,
      h]

/-- `lem:print`, paper/paper.tex: both
actual original-pool branches return the same exact count and ordered
native rows to the concrete once-only resize finalizer. -/
theorem actualBankRequest_answer (r : NativeKidsRequest) :
    StageMain.Tagged.taggedAnswer (fun q : FirstBankRequest => q.val.resizeTailRequest.word)
      (fun q : SecondBankRequest => q.val.resizeTailRequest.word) (actualBankRequest r) =
      r.resizeTailRequest.word := by
  unfold actualBankRequest
  split <;> rfl

end NearQuarticWires.StageNativeKids
