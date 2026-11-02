import Proof.Quartic.StagePrint.TermsCarrierTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.CarrierEnvelope
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- `lem:print`, paper/paper.tex: actual
recovery metadata are retained once around the original compiled
carrier, before its source is replaced by native table input. -/
noncomputable def word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  Top.loadRec (natWord (r.prime^r.child.selected.1.e))
    (frame (TermsCarrier.word r)) (natWord r.child.cellCall.ncol)
    [] [] [] [] [] [] [] []

/-- `lem:print` and `prop:time`, paper/paper.tex: the real finite carrier alone yields both actual
metadata codecs and retains its original source exactly once. -/
abbrev Producer (B1 B2 : ℕ) :=
  (budget : Greedy.PrintRequest B1 B2→ℕ) ×
    WordFunction (Greedy.PrintRequest B1 B2) TermsCarrier.word (fun r=>frame (word r)) budget

end NearQuarticWires.StagePrint.CarrierEnvelope
