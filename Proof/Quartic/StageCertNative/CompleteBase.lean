import Proof.Quartic.StageCertNative.NativeInput

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertificateControl

section
variable {tupleBudget : StageTuple.TermCutRequest→ℕ}
variable (T : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word
  (fun r=>frame r.output) tupleBudget)
variable (h : Bindings.Williams14.Williams14_Corollary4_4)

noncomputable def completeBaseBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  4*nativeInputBudget (termBudget:=weakTermBudget (tupleBudget:=tupleBudget)) r+
    4*Output.budget h (nativeHeaderRequest r)+12

/-- `lem:print` and `prop:time`, paper/paper.tex: the entire original preparation and test index are
processed by the actual source, exact expansion, original child tuples,
per-walk signed equality conversion, one whole native table and signed
output prefix. The two concrete subroutines are bound at the final
public machine; no extra runtime field is introduced here. -/
noncomputable def completeBaseWordFunctionOf (N : Output.Producer h) (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (NearCubicWires.RepairRepresentation.natWord ((actualTable r).q+1)++
        (actualTable r).output)) (completeBaseBudget (tupleBudget:=tupleBudget) h) := by
  let f:=Program.WordFunction.pipe
    (nativeInputWordFunctionOf (weakTermWordFunctionOf T B1 B2))
    (restrictWordFunction N (fun r : IndexedRequest B1 B2=>nativeHeaderRequest r))
  refine ⟨f.program,?_⟩
  intro r
  simpa only [completeBaseBudget,nativeHeaderRequest_output] using f.realizes r

end
end NearQuarticWires.StageCertNative
