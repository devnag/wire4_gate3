import Proof.Quartic.StageGreedyEntry.HeaderBound
import Proof.Quartic.StageGreedyEntry.FormatBound
import Proof.Quartic.StageGreedyEntry.Budget
import Proof.Quartic.StageCertNative.DoubleFrame
import Proof.Quartic.Program.Pipe

/-!
# The common native header from one actual entry

Paper: `lem:print` and `prop:time`, paper/paper.tex.

The literal entry bytes pass through the closed shared formatter, the framed tuple request is framed once
more, and the header extractor reads the four original star scalars and the common field width from it:
`headerProducer` writes exactly `frame (globalHeader r.source)`. Its clock meets the selected
per-entry bound (`headerProducer_bound`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint StageGreedyCollector

/-- `prop:time`, paper/paper.tex: the second frame is linear in the formatted request. -/
theorem doubleFrame_bound (B1 B2 : ℕ) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>2000*(r.termRequest.word.length+1)+2) := by
  refine ebb_mono (ebb_add (ebb_smul (formatter_bound B1 B2) 2000) (ebb_const 2002)) (fun r=>?_)
  have h:=Control.output_length_le (formatter B1 B2) r
  simp only [frame_length] at h
  omega

/-- `lem:print`, paper/paper.tex: the common native header produced from
the literal entry bytes, with no supplied geometry or width. -/
noncomputable def headerProducer (B1 B2 : ℕ) : HeaderProducer B1 B2 :=
  ⟨_,Program.WordFunction.pipe
    (Program.WordFunction.pipe (formatter B1 B2)
      (StageCertNative.doubleFrameWordFunction (fun r : GreedyEntry.Request B1 B2=>r.termRequest.word)))
    (headerExtract B1 B2).2⟩

/-- `prop:time`, paper/paper.tex: the header clock meets the selected bound. -/
theorem headerProducer_bound (B1 B2 : ℕ) : EntryBudgetBound (headerProducer B1 B2).1 :=
  ebb_pipe (ebb_pipe (formatter_bound B1 B2) (doubleFrame_bound B1 B2)) (headerExtract_bound B1 B2)

end NearQuarticWires.StageGreedyEntry
