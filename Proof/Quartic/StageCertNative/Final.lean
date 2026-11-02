import Proof.Quartic.StageCertNative.CompleteOutput
import Proof.Quartic.StageCertNative.CompleteBaseCost
import Proof.Quartic.StageCertNative.PriceTuple
import Proof.Quartic.StagePrintTuple.Final

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual complete original-child
Tuple implementation has its proved sharp occurrence price at every
actual CERT term, with no source or clock premise. -/
theorem actual_tuple_price (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termRequest r.base r.index).budget) 2 := by
  obtain ⟨C,E,_hC,_hE,hledger⟩:=StageTuple.budget_sharp
  exact price_tuple_of_ledger C E hledger

/-- `prop:time`, paper/paper.tex: the
complete actual BASE clock includes original source acquisition,
exact integer expansion, original child tuples, signed equality
conversion, the one native table and its signed output frame. -/
noncomputable def baseNativeBudget
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ)
    (r : IndexedRequest B1 B2) : ℕ :=
  completeBaseBudget (tupleBudget:=StageTuple.TermCutRequest.budget) h r

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: literal original preparation and the actual
five-field test metadata produce the complete signed native table,
prefixed by its computed reconstruction width. The published Williams
input is the only external algorithm input. -/
noncomputable def baseNativeWordFunction
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (natWord ((actualTable r).q+1)++(actualTable r).output))
      (baseNativeBudget h B1 B2) :=
  baseWordFunctionWithTuple StageTuple.termCutWordFunction h B1 B2

/-- `prop:time`, paper/paper.tex: the
actual complete BASE machine satisfies the exact original-call and
dispatched three-term runtime bound on every proposed witness. -/
theorem baseNativeBudget_bound
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    ∃K E : ℕ,∀r : IndexedRequest B1 B2,
      baseNativeBudget h B1 B2 r≤K*((callWord r.prepared.call).length+1)^E+
        K*Program.runEnvelope B1 B2 E r.prepared.call :=
  completeBase_ledger h (actual_tuple_price B1 B2)

end NearQuarticWires.StageCertNative
