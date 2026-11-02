import Proof.Quartic.StagePrintFinal.Envelope
import Proof.Quartic.StageGreedyCollector.Final

set_option autoImplicit false

namespace NearQuarticWires.StagePrintFinal

open NearCubicWires

/-- `lem:print`, `lem:residue` and `prop:time`,
paper/paper.tex:
the complete actual table printer starts at the original request,
executes the genuine source compiler, carrier envelope, whole-cut
collector, two metadata-preserving maps, native header and published
native recovery, and prints the exact raw centered table. Its same
physical budget has the selected column cost plus one additive
polynomial in the literal raw-index length. No source, table, program,
producer, code, semantic or clock argument remains. -/
noncomputable def printField
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    Program.PrintField B1 B2 :=
  fieldOfCollector h (StageGreedyCollector.collectorProducer B1 B2)
    (StageGreedyCollector.collectorProducer_selected B1 B2)

end NearQuarticWires.StagePrintFinal
