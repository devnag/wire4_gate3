import Proof.Quartic.StagePrint.GreedyCollectorTarget
import Proof.Quartic.StagePrint.EntryFormatRequest

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairRepresentation

/-- `lem:print`, paper/paper.tex: every actual
entry's native weak-field width equals the single common width used
in the global concatenation, including zero-weight walk entries. -/
theorem GreedyEntry.Request.fieldWidth_eq {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    r.termRequest.stackWidth+1=GreedyCollector.fieldWidth r.source := by
  rfl

/-- `lem:print`, paper/paper.tex: the shared
formatter constructs the unchanged actual tuple request. -/
theorem EntryFormat.ofGreedy_termRequest {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (EntryFormat.ofGreedy r).termRequest=r.termRequest := by
  rfl

/-- `lem:print`, paper/paper.tex: the shared
formatter input is the actual small retained context followed by one
unchanged real compiled entry, with the original arity leading. -/
theorem EntryFormat.ofGreedy_word {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (EntryFormat.ofGreedy r).word=
      natWord r.source.child.call.n++Context.word r.prepared++
        TermsCarrier.entryWord r.source r.index := by
  simp only [EntryFormat.Request.word,EntryFormat.Request.contextWord,
    EntryFormat.Request.countsWord,EntryFormat.ofGreedy,
    GreedyEntry.Request.rowContext,GreedyEntry.Request.prepared,
    Context.word,Context.countsWord,Context.geometryWord,Context.header,
    GreedyEntry.Request.degree,GreedyEntry.Request.modulus,GreedyEntry.Request.terms,
    TermsCarrier.entryWord,StageLift.sourceWalkPacket,List.append_assoc,Cells.ParameterRules.seed_N]

end NearQuarticWires.StagePrint
