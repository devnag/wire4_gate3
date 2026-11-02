import Proof.Quartic.StageCertNative.PriceBindings
import Proof.Quartic.StageCertNative.NativeInput
import Proof.Quartic.StageCertNativePoolCost.Whole

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: joining
two computed finite outputs uses a linear sum of their real clocks
and lengths, and therefore preserves one original-column factor. -/
theorem OriginalPrice.framedPair {B1 B2 : ℕ}
    {input left right : IndexedRequest B1 B2→List Bool}
    {lb rb : IndexedRequest B1 B2→ℕ}
    (hi : OriginalPrice (fun r=>(input r).length))
    (hl : OriginalPrice (fun r=>(left r).length))
    (hr : OriginalPrice (fun r=>(right r).length))
    (hbl : OriginalPrice lb) (hbr : OriginalPrice rb) :
    OriginalPrice (fun r=>2*StageRecovery.FramedPair.cost (input:=input)
      (left:=left) (right:=right) (lb:=lb) (rb:=rb) r+2) := by
  have h2l:=hbl.mul_arity (g:=fun _=>2) (JobPrice.constant 2)
  have h2r:=hbr.mul_arity (g:=fun _=>2) (JobPrice.constant 2)
  have hs:=((hi.add hl).add hr).add (OriginalPrice.constant 1)
  have h300:=hs.mul_arity (g:=fun _=>300) (JobPrice.constant 300)
  have hh:=(((h2l.add h2r).add h300).mul_arity (g:=fun _=>2)
    (JobPrice.constant 2)).add (OriginalPrice.constant 2)
  refine hh.mono ?_
  intro r
  unfold StageRecovery.FramedPair.cost
  exact le_of_eq (by ring)

theorem original_wholeWeak_length (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>(wholeWeakWord r).length) := by
  refine (original_native_stream B1 B2).mono ?_
  intro r
  exact le_of_eq (congrArg List.length (wholeWeakWord_eq_nativeStream r))

/-- `prop:time`, paper/paper.tex: the actual
source-to-native-input clock combines the concrete selected source
and unchanged whole-loop reserve, including the numeric index writer. -/
theorem original_nativeInput_budget {B1 B2 : ℕ}
    {termBudget : TermJob B1 B2→ℕ} (ht : JobPrice termBudget 4) :
    OriginalPrice (nativeInputBudget (termBudget:=termBudget)) := by
  have hp : OriginalPrice (wholeWeakOriginalBudget (termBudget:=termBudget)) :=
    StageCertNativePoolCost.wholeWeak_cost B1 B2 termBudget ht
  exact (original_base_word B1 B2).framedPair
    (OriginalPrice.of_job_zero (f:=fun r : IndexedRequest B1 B2=>(nativeFieldsWord r).length)
      (price_nativeFieldsLength B1 B2))
    (original_wholeWeak_length B1 B2) (original_nativeFields_budget B1 B2) hp

end NearQuarticWires.StageCertNative
