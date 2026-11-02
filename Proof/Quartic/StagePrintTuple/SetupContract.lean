import Proof.Quartic.StagePrintTuple.SourceLoad
import Proof.Quartic.StagePrintTuple.Coefficient

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: one actual
preparation retains the original source and Terms once, frames the real
context, computes the common field width and row count, and obtains
both fixed signed constants from their genuine coefficient machines. -/
def TermCutRequest.preparedFields (r : TermCutRequest) : Fin 11→List Bool :=
  ![frame (callWord r.header.call),
    frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord),
    frame r.contextWord,termsWord r.terms,natWord (r.stackWidth+1),
    (CoefficientRequest.mk (r.stackWidth+1) 0).output,
    (CoefficientRequest.mk (r.stackWidth+1) 1).output,
    natWord (r.rowDimension+1),natWord r.degree,frame (natWord (r.stackWidth+1)),[]]

/-- `lem:print`, paper/paper.tex: the internal
prepared word has the existing eleven-field framing, with the complete
original Terms in exactly one field and no supplied child pool. -/
def TermCutRequest.preparedWord (r : TermCutRequest) : List Bool :=
  Top.loadRec (r.preparedFields 0) (r.preparedFields 1) (r.preparedFields 2)
    (r.preparedFields 3) (r.preparedFields 4) (r.preparedFields 5) (r.preparedFields 6)
    (r.preparedFields 7) (r.preparedFields 8) (r.preparedFields 9) (r.preparedFields 10)

/-- `prop:time`, paper/paper.tex: the small
structural preparation magnitude excludes the full Terms list and its
length. Original source bytes and real fixed field widths fund every
separate arithmetic call. -/
def TermCutRequest.setupStructuralMagnitude (r : TermCutRequest) : ℕ :=
  r.header.call.n+r.stackWidth+(callWord r.header.call).length+
    ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord).length+
    r.contextWord.length+(natWord r.degree).length+10

/-- `prop:time`, paper/paper.tex: preparation
has linear cost in the complete source bytes plus a fixed polynomial
in the separate original source and stacking-width magnitude. -/
abbrev TupleSetupCost (budget : TermCutRequest→ℕ) : Prop :=
  ∃C E:ℕ,∀r,budget r≤C*(r.word.length+1)+C*r.setupStructuralMagnitude^E

end NearQuarticWires.StageTuple
