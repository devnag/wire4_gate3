import Proof.Quartic.StageNativeKids.Budget
import Proof.Quartic.StageNativeKidsPool.Machine
import Proof.Quartic.StageNativeKidsTail.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: the
physically computed original bank invokes one of the two actual cold
original-child pool machines, preserving the exact computed count and
original ordered raw native rows. -/
noncomputable def actualPoolWordFunction :
    WordFunction NativeKidsRequest NativeKidsRequest.bankWord
      (fun r => frame r.resizeTailRequest.word) selectedPoolBudget :=
  taggedPoolWordFunction StageNativeKidsPool.firstPoolWordFunction
    StageNativeKidsPool.secondPoolWordFunction

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual original eleven-field source
computes its original-order native pool and count, through the actual
role selector and concrete original-bank machines. -/
noncomputable def poolSourceWordFunction :
    WordFunction NativeKidsRequest NativeKidsRequest.word
      (fun r => frame r.resizeTailRequest.word) poolSourceBudget :=
  Program.WordFunction.pipe sourceBankWordFunction actualPoolWordFunction

/-- `lem:print`, paper/paper.tex: the
actual once-only stream resizer preserves the computed child count and
all original native fields, emitting the exact original caller reply. -/
noncomputable def actualTailWordFunction :
    WordFunction NativeKidsRequest (fun r => r.resizeTailRequest.word)
      NativeKidsRequest.output (fun r => r.resizeTailRequest.budget) :=
  ⟨StageNativeKidsTail.resizeTailWordFunction.program, by
    intro r
    simpa only [resizeTailRequest_output] using
      StageNativeKidsTail.resizeTailWordFunction.realizes r.resizeTailRequest⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal original eleven-field request
computes the exact native child count and complete original-order
signed pool, using actual source selection, original compilation,
counting, ordered row calls and one stream-resize tail. -/
noncomputable def nativeKidsWordFunction :
    WordFunction NativeKidsRequest NativeKidsRequest.word
      NativeKidsRequest.output NativeKidsRequest.budget :=
  Program.WordFunction.pipe poolSourceWordFunction actualTailWordFunction

end NearQuarticWires.StageNativeKids
