import Proof.Quartic.StageCertNative.ExactSource
import Proof.Quartic.StageCertNative.ExpandFrame

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

noncomputable def framedTermsBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*exactFormulaBudget r+
    4*(2*expandFrameSteps NearCubicGates.Close.Expand.expansionMachine
      ⟨r.packet.arity,r.formula⟩+2)+12

/-- `lem:print` and `prop:time`, paper/paper.tex: actual original prefix-index bytes produce one framed
exact Terms field. Every signed mask and failed column is preserved;
the complete source, formatter, projection, integer expansion and
counted Terms framing are actual fixed ordinary machines. -/
noncomputable def framedTermsWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) indexedMomentWord
      (fun r=>frame (termsWord (exactTerms r))) framedTermsBudget :=
  Program.WordFunction.pipe (exactFormulaWordFunction B1 B2)
    (restrictWordFunction (framedExpandWordFunction NearCubicGates.Close.Expand.expansionMachine)
      (fun r : MomentRequest B1 B2=>⟨r.packet.arity,r.formula⟩))

end NearQuarticWires.StageCertNative
