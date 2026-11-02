import Proof.Quartic.StageCertNative.CompleteBase
import Proof.Quartic.StageCertNativeOutput.Main

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: the exact
whole-source constructor invokes the actual five-field native-output
program, with its existing published Williams multiplication input.
Only the original exact Tuple program remains to be bound. -/
noncomputable def baseWordFunctionWithTuple
    {tupleBudget : StageTuple.TermCutRequest→ℕ}
    (T : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word
      (fun r=>frame r.output) tupleBudget)
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (NearCubicWires.RepairRepresentation.natWord ((actualTable r).q+1)++
        (actualTable r).output)) (completeBaseBudget (tupleBudget:=tupleBudget) h) :=
  completeBaseWordFunctionOf T h (StageCertNativeOutput.nativeOutputWordFunction h) B1 B2

end NearQuarticWires.StageCertNative
