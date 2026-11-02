import Proof.Quartic.StageRecovery.NativeExtractor
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: actual outer
extraction and the published-source native table call have additive
physical costs on the ordinary machine's disjoint sequential banks. -/
noncomputable def nativeProducerBudget
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeRequest) : ℕ :=
  4 * r.extractorBudget +
    4 * (2 * NativeTableFrame.steps (NativeTableFrame.publishedAlgorithm h) r.table + 2) + 12

/-- `lem:print`, paper/paper.tex:
the actual literal modulus/table/target outer word produces the complete
framed native record packet, through the published multiplication
binding and real fixed-input extraction rather than prepared call tapes. -/
noncomputable def nativeProducerWordFunction
    (h : Bindings.Williams14.Williams14_Corollary4_4) :
    WordFunction NativeRequest NativeRequest.word (fun r => frame r.table.output)
      (nativeProducerBudget h) := by
  let f := NativeTableFrame.publishedWordFunction h
  let g : WordFunction NativeRequest (fun r => r.table.word) (fun r => frame r.table.output)
      (fun r => 2 * NativeTableFrame.steps (NativeTableFrame.publishedAlgorithm h) r.table + 2) :=
    ⟨f.program, fun r => f.realizes r.table⟩
  exact Program.WordFunction.pipe nativeExtractorWordFunction g

end NearQuarticWires.StageRecovery
