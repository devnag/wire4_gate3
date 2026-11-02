import Proof.Quartic.StageCertNative.CountedSourceMachine
import Proof.Quartic.StageCertNative.DoubleFrame

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces.Formats

noncomputable def jobNestedTermsBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*jobTermsBudget r+4*(2000*((termsWord (exactTerms r.moment)).length+1)+2)+12

/-- `lem:print` and `prop:time`, paper/paper.tex: a literal Terms frame is itself a framed payload for
the exact tuple request assembler. Its delimiters are copied by an
actual frame scan, not inferred from a semantic output-length oracle. -/
noncomputable def jobNestedTermsWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (frame (termsWord (exactTerms r.moment)))) jobNestedTermsBudget :=
  Program.WordFunction.pipe (jobTermsWordFunction B1 B2)
    (doubleFrameWordFunction (fun r : TermJob B1 B2=>termsWord (exactTerms r.moment)))

end NearQuarticWires.StageCertNative
