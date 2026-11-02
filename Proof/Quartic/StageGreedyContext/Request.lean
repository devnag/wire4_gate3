import Proof.Quartic.StageGreedyCollector.ContextTarget

/-!
# Literal preparation and unchanged carrier suffix

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the
context pass receives an actual prepared source followed by arbitrary
unchanged bytes, so no numeric count or decoded entry is supplied. -/
structure Request (B1 B2 : ℕ) where
  prepared : StageCertTests.PreparedScheduleRequest B1 B2
  suffix : List Bool

/-- `lem:print`, paper/paper.tex: the
actual finite source is the same literal preparation used by the
fixed common-context machine. -/
noncomputable def Request.prep {B1 B2 : ℕ} (r : Request B1 B2) : List Bool := r.prepared.word

/-- `lem:print`, paper/paper.tex: one
finite preparation byte count precedes the raw preparation and the
unchanged binary count and entry suffix. -/
noncomputable def Request.word {B1 B2 : ℕ} (r : Request B1 B2) : List Bool :=
  natWord r.prep.length++r.prep++r.suffix

/-- `lem:print`, paper/paper.tex: the
original arity begins the one actual context computed from the
preparation, independently of the arbitrary carrier suffix. -/
def Request.context {B1 B2 : ℕ} (r : Request B1 B2) : List Bool :=
  natWord r.prepared.call.n++StagePrint.Context.word r.prepared

/-- `lem:print`, paper/paper.tex: the
context pass replaces the consumed preparation by its one framed
common context and copies the unchanged suffix exactly once. -/
noncomputable def Request.output {B1 B2 : ℕ} (r : Request B1 B2) : List Bool :=
  frame (frame r.context++r.suffix)

/-- `sec:params` and `lem:print`, paper/paper.tex: the actual preparation begins with
its success marker and original encoded arity. -/
theorem Request.prep_prefix {B1 B2 : ℕ} (r : Request B1 B2) :
    ∃rest,r.prep= true::(natWord r.prepared.call.n++rest) := by
  rw [Request.prep,r.prepared.word_eq]
  unfold callWord
  simp only [List.append_assoc]
  exact ⟨_,rfl⟩

/-- `lem:print`, paper/paper.tex: the
one context computation is the actual closed source machine,
restricted to the original preparation of each carrier. -/
noncomputable def setup (B1 B2 : ℕ) :
    WordFunction (Request B1 B2) Request.prep
      (fun r=>frame (StagePrint.Context.word r.prepared))
      (fun r=>(StagePrintContext.contextProducer B1 B2).1 r.prepared) where
  program:=(StagePrintContext.contextProducer B1 B2).2.program
  realizes r:=(StagePrintContext.contextProducer B1 B2).2.realizes r.prepared

/-- Step 3 and `lem:print`, paper/paper.tex: the real compiled carrier determines the original
preparation and all unchanged low-first entries, including zeros. -/
noncomputable def actualRequest {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : Request B1 B2 where
  prepared:=StagePrint.GreedyCollector.prepared r
  suffix:=natWord (r.child.cellCall.seed.N^8)++(List.ofFn (StagePrint.TermsCarrier.entryWord r)).flatten

/-- `lem:print`, paper/paper.tex: no
additional source or semantic field enters the real frontend input. -/
theorem actualRequest_word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualRequest r).word=StagePrint.TermsCarrier.word r := by
  rw [StagePrint.TermsCarrier.word,StageLift.preparedWordOf_eq_prepWord]
  simp only [actualRequest,Request.word,Request.prep,StagePrint.GreedyCollector.prepared,
    StageCertTests.PreparedScheduleRequest.word,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the
real frontend output has precisely the frozen one-context framing
and all original binary count and entry bytes in their original order. -/
theorem actualRequest_output {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualRequest r).output=frame (StageGreedyCollector.contextualWord r) := by
  simp only [actualRequest,Request.output,Request.context,StageGreedyCollector.contextualWord,
    StageGreedyCollector.contextWord,StagePrint.GreedyCollector.prepared,List.append_assoc]

end NearQuarticWires.StageGreedyContext
