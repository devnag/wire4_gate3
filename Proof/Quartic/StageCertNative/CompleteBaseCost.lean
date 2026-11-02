import Proof.Quartic.StageCertNative.CompleteBase
import Proof.Quartic.StageCertNative.PriceAssembly
import Proof.Quartic.StageCertNative.PriceLedger

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: the
complete actual exact-source, signed-cut and native-output clock fits
one original-column envelope once the concrete Tuple clock is charged
at its sharp original-child census. -/
theorem original_completeBase_budget
    {B1 B2 : ℕ} {tupleBudget : StageTuple.TermCutRequest→ℕ}
    (h : Bindings.Williams14.Williams14_Corollary4_4)
    (htuple : JobPrice (fun r : TermJob B1 B2=>tupleBudget (termRequest r.base r.index)) 2) :
    OriginalPrice (completeBaseBudget (B1:=B1) (B2:=B2) (tupleBudget:=tupleBudget) h) := by
  have ht:=original_nativeInput_budget (price_weakTerm htuple)
  have hn:=original_native_output_budget h B1 B2
  have hh:=((ht.mul_arity (g:=fun _=>4) (JobPrice.constant 4)).add
    (hn.mul_arity (g:=fun _=>4) (JobPrice.constant 4))).add (OriginalPrice.constant 12)
  refine hh.mono ?_
  intro r
  unfold completeBaseBudget
  omega

/-- `prop:time`, paper/paper.tex: the
complete actual BASE clock has the exact public call-word plus
dispatched-envelope bound consumed by certificate assembly. -/
theorem completeBase_ledger
    {B1 B2 : ℕ} {tupleBudget : StageTuple.TermCutRequest→ℕ}
    (h : Bindings.Williams14.Williams14_Corollary4_4)
    (htuple : JobPrice (fun r : TermJob B1 B2=>tupleBudget (termRequest r.base r.index)) 2) :
    ∃K E : ℕ,∀r : IndexedRequest B1 B2,
      completeBaseBudget (tupleBudget:=tupleBudget) h r≤
        K*((callWord r.prepared.call).length+1)^E+
        K*Program.runEnvelope B1 B2 E r.prepared.call :=
  (original_completeBase_budget h htuple).ledger

end NearQuarticWires.StageCertNative
