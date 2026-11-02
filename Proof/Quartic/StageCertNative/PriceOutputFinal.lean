import Proof.Quartic.StageCertNative.PriceOutput

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StageCertificateControl

theorem price_nativeFieldsLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(nativeFieldsWord r.base).length) 0 := by
  have hh:=(price_geometryLength B1 B2).add
    (((price_commonWidth B1 B2).add (JobPrice.constant 1)).natWordLength)
  simpa only [nativeFieldsWord,List.length_append] using hh

theorem original_native_input (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>(nativeHeaderRequest r).word.length) := by
  have hf:=OriginalPrice.of_job_zero
    (f:=fun r : IndexedRequest B1 B2=>(nativeFieldsWord r).length)
    (price_nativeFieldsLength B1 B2)
  have hh:=hf.add (original_native_stream B1 B2)
  refine hh.mono ?_
  intro r
  have hs : (nativeHeaderRequest r).stream=wholeWeakWord r :=
    (wholeWeakWord_eq_nativeStream r).symm
  rw [nativeHeaderRequest_word,List.length_append,hs]

/-- `prop:time`, paper/paper.tex: the
actual five-field native printer, full Williams table computation and
signed-output framing use one original-column envelope, with only a
fixed original-arity polynomial multiplier. -/
theorem original_native_output_budget
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>Output.budget h (nativeHeaderRequest r)) := by
  have hp : JobPrice (fun r : TermJob B1 B2=>
      (nativeHeaderRequest r.base).parameters.n+(actualTable r.base).matrix.p+2) 0 := by
    refine ((price_arity B1 B2).add (price_tableWidth B1 B2)).mono ?_
    intro r
    change r.moment.call.n+(actualTable r.base).matrix.p+2≤
      r.moment.call.n+((actualTable r.base).q+3)
    unfold StagePrint.TableRequest.q
    omega
  have hfactor:=(JobPrice.constant (10^50)).mul (hp.pow 60)
  have hsum:=(((original_native_input B1 B2).add (original_count_price B1 B2)).add
    (original_native_steps (StageRecovery.NativeTableFrame.publishedAlgorithm h) B1 B2)).add
    (OriginalPrice.constant 1)
  have hh:=hsum.mul_arity (g:=fun r=>10^50*
    ((nativeHeaderRequest r).parameters.n+(actualTable r).matrix.p+2)^60) hfactor
  refine hh.mono ?_
  intro r
  unfold Output.budget
  exact le_of_eq (Nat.mul_comm _ _)

end NearQuarticWires.StageCertNative
