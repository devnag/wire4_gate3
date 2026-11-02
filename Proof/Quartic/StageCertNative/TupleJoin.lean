import Proof.Quartic.StageCertNative.EqualityFormatMachine
import Proof.Quartic.StageEqualityRows.Final

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

section
variable {tupleBudget : StageTuple.TermCutRequest→ℕ}
variable (T : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word
  (fun r=>frame r.output) tupleBudget)

noncomputable def tupleSourceBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*termRequestSourceBudget r+4*tupleBudget (termRequest r.base r.index)+12

/-- `lem:print`, paper/paper.tex: physical
Tuple construction is invoked on the exact source-derived eleven
fields; the original finite equality stream is its actual output. -/
noncomputable def tupleSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (termRequest r.base r.index).output) (tupleSourceBudget (tupleBudget:=tupleBudget)) :=
  Program.WordFunction.pipe (termRequestSourceWordFunction B1 B2)
    (restrictWordFunction T (fun r : TermJob B1 B2=>termRequest r.base r.index))

noncomputable def nestedTupleBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*tupleSourceBudget (tupleBudget:=tupleBudget) r+
    4*(2000*((termRequest r.base r.index).output.length+1)+2)+12

noncomputable def nestedTupleWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (frame (termRequest r.base r.index).output)) (nestedTupleBudget (tupleBudget:=tupleBudget)) :=
  Program.WordFunction.pipe (tupleSourceWordFunction T B1 B2)
    (doubleFrameWordFunction (fun r : TermJob B1 B2=>(termRequest r.base r.index).output))

noncomputable def equalitySourceBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  2*StageRecovery.FramedPair.cost (input:=TermJob.word)
    (left:=fun r : TermJob B1 B2=>(exactEntry r.moment).word)
    (right:=fun r : TermJob B1 B2=>frame (termRequest r.base r.index).output)
    (lb:=entrySourceBudget) (rb:=nestedTupleBudget (tupleBudget:=tupleBudget)) r+2

/-- `lem:print`, paper/paper.tex: exact source
and actual signed equality output are assembled with their real frame
delimiters; no row count or output-length value is supplied. -/
noncomputable def equalitySourceWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word (fun r=>frame (equalityEntryWord r))
      (equalitySourceBudget (tupleBudget:=tupleBudget)) :=
  StageRecovery.FramedPair.wordFunction (entrySourceWordFunction B1 B2)
    (nestedTupleWordFunction T B1 B2)

noncomputable def equalityJobBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*equalitySourceBudget (tupleBudget:=tupleBudget) r+4*equalityFormatBudget r+12

noncomputable def equalityJobWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (StagePrint.Downstream.equalityRowsInput (termNativeRequest r)))
      (equalityJobBudget (tupleBudget:=tupleBudget)) :=
  Program.WordFunction.pipe (equalitySourceWordFunction T B1 B2) (equalityInputWordFunction B1 B2)

noncomputable def weakTermBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*equalityJobBudget (tupleBudget:=tupleBudget) r+
    4*(10^30*(NearCubicWires.WireExponent3_5.PrimT.C4Geo.width
      (termNativeRequest r).parameters+(termNativeRequest r).fieldWidth+2)^20*
        (((termNativeRequest r).cuts.flatMap
          (MatrixScoreBatch.cutWord (termNativeRequest r).fieldWidth)).length+1)^2)+12

/-- `lem:print` and `prop:time`, paper/paper.tex: each actual original term is transformed into its
complete signed two-weak-cut stream before whole-test concatenation.
The equality conversion is applied separately to every actual walk. -/
noncomputable def weakTermWordFunctionOf (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word (fun r=>frame (termWeakWord r))
      (weakTermBudget (tupleBudget:=tupleBudget)) :=
  Program.WordFunction.pipe (equalityJobWordFunction T B1 B2)
    (restrictWordFunction StageEqualityRows.equalityRowsPrinter termNativeRequest)

end

end NearQuarticWires.StageCertNative
