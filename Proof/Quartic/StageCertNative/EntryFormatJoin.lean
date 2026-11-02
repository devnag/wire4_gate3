import Proof.Quartic.StageCertNative.EntrySource
import Proof.Quartic.StageCertNative.EntryScale
import Proof.Quartic.StageCertNative.Cuts
import Proof.Quartic.StagePrint.EntryFinal

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- `lem:print`, paper/paper.tex: membership
in the fixed formatter domain adds a mathematical size proof only;
the physical source still contains exactly the same bytes. -/
noncomputable def boundedExactEntry {B1 B2 : ℕ} (r : TermJob B1 B2) :
    StagePrint.EntryFormat.BoundedRequest
      (entrySizingCoefficient B1 B2) (entrySizingExponent B1 B2) false where
  toRequest:=exactEntry r.moment
  size_bound:=exactEntry_sizing r

noncomputable def actualFormatterBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  StagePrint.EntryFormat.formatterBudget (boundedExactEntry r)

/-- `lem:print`, paper/paper.tex: this is the
shared actual cold formatter restricted to the original exact source
family; its public machine has no width, pool or row provider premise. -/
noncomputable def actualFormatterWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) (fun r=>(exactEntry r.moment).word)
      (fun r=>frame (termRequest r.base r.index).word) actualFormatterBudget :=
  restrictWordFunction (StagePrint.EntryFormat.formatterWordFunction
    (entrySizingCoefficient B1 B2) (entrySizingExponent B1 B2) false) boundedExactEntry

noncomputable def termRequestSourceBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*entrySourceBudget r+4*actualFormatterBudget r+12

/-- `lem:print` and `prop:time`, paper/paper.tex: original counted source alone is transformed into
the actual eleven-field Tuple request. All exact source construction,
signed expansion, framing, native width arithmetic and copying are paid. -/
noncomputable def termRequestSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (termRequest r.base r.index).word) termRequestSourceBudget :=
  Program.WordFunction.pipe (entrySourceWordFunction B1 B2) (actualFormatterWordFunction B1 B2)

end NearQuarticWires.StageCertNative
