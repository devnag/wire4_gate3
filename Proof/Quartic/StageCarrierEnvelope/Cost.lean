import Proof.Quartic.StageCarrierEnvelope.Producer

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)

/-- `prop:time`, paper/paper.tex: reading
the finite preparation length costs a polynomial of that actual
prefix, while the skipped headers are charged by their byte lengths. -/
theorem prefixSteps_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    prefixSteps r≤1000*((StageLift.preparedWordOf r).length+1)^2+
      100*((StagePrint.TermsCarrier.word r).length+1) := by
  let P:=(StageLift.preparedWordOf r).length
  have hn:=NearCubicGates.Close.Dispatch.natBitLength_le_succ P
  have hp:=NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le P
  have hpre:=prefix_length_le_carrier r
  simp only [firstPrefix,List.length_append] at hpre
  unfold prefixSteps
  change (natBitLength P+2)*(40*2^natBitLength P+40)+100*(P+_+1)≤_
  have ha : natBitLength P+2≤3*(P+1) := by omega
  have hb : 40*2^natBitLength P+40≤120*(P+1) := by omega
  have hm:=Nat.mul_le_mul ha hb
  nlinarith only [hm,hpre]

/-- `prop:time`, paper/paper.tex: all
source copying and encoded first-entry metadata are linear in the
actual carrier, with polynomial dependence only on its finite prefix. -/
theorem bodySteps_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    bodySteps r≤10^6*((StagePrint.TermsCarrier.word r).length+1)*
      ((StageLift.preparedWordOf r).length+1)^3 := by
  let I:=(StagePrint.TermsCarrier.word r).length
  let P:=(StageLift.preparedWordOf r).length
  have hpre:=prefixSteps_bound r
  have hq:=modulus_length_le_carrier r
  have hcol:=column_codec_length r
  have hn:=original_arity_le r
  change prefixSteps r≤1000*(P+1)^2+100*(I+1) at hpre
  change (natWord (r.prime^r.child.selected.1.e)).length≤I at hq
  change r.child.call.n≤P at hn
  have hpow : 1≤(P+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hP : P+1≤(P+1)^3 := Nat.le_self_pow (by decide) _
  have hP2 : (P+1)^2≤(P+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hi : I+1≤(I+1)*(P+1)^3 := Nat.le_mul_of_pos_right _ (by omega)
  have hp : (P+1)^3≤(I+1)*(P+1)^3 := Nat.le_mul_of_pos_left _ (by omega)
  unfold bodySteps
  simp only [frame_length]
  change 200*(I+1)+1+prefixSteps r+1+1000*((natWord (r.prime^r.child.selected.1.e)).length+
    (2*I+1)+(2*(natWord r.child.cellCall.ncol).length+1)+1)≤_
  nlinarith only [hpre,hq,hcol,hn,hi,hp,hP,hP2]

/-- `prop:time`, paper/paper.tex: the
SAME complete cold budget is linear in actual Terms bytes and has
only fixed polynomial overhead in the original finite preparation. -/
theorem envelopeBudget_prefix_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    envelopeBudget r≤4*metadataBudget r+10^7*((StagePrint.TermsCarrier.word r).length+1)*
      ((StageLift.preparedWordOf r).length+1)^3 := by
  have hb:=bodySteps_bound r
  have hP : 1≤((StageLift.preparedWordOf r).length+1)^3:=Nat.one_le_pow _ _ (by omega)
  have hi : (StagePrint.TermsCarrier.word r).length+1≤
      ((StagePrint.TermsCarrier.word r).length+1)*((StageLift.preparedWordOf r).length+1)^3 :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold envelopeBudget envelopeSteps
  nlinarith only [hb,hi]

/-- `prop:time`, paper/paper.tex: original
normalized-call bounds price this SAME actual envelope producer;
no raw-index term is multiplied by the center count or source length. -/
theorem carrierEnvelopeProducer_budget (B1 B2 : ℕ) : ∃K e : ℕ,∀r : Greedy.PrintRequest B1 B2,
    (carrierEnvelopeProducer B1 B2).1 r≤K*((StagePrint.TermsCarrier.word r).length+1)*(r.child.call.n+1)^e := by
  obtain ⟨K0,e0,h0⟩:=metadataBudget_linear B1 B2
  let C:=StageMain.Compact.capacityCoefficient B1
  let E:=StageMain.Compact.capacityExponent B1 B2
  refine ⟨4*K0+10^7*(C+1)^3,e0+E*3,fun r=>?_⟩
  have hprep:=StageMain.Compact.compactInput_length_arity r.child.dispatched r.child.witness
  change (StageLift.preparedWordOf r).length≤C*(r.child.call.n+1)^E at hprep
  have h1 : 1≤(r.child.call.n+1)^E:=Nat.one_le_pow _ _ (by omega)
  have hp : (StageLift.preparedWordOf r).length+1≤(C+1)*(r.child.call.n+1)^E := by nlinarith only [hprep,h1]
  have hp3:=Nat.pow_le_pow_left hp 3
  rw [mul_pow,←pow_mul] at hp3
  have he0 : (r.child.call.n+1)^e0≤(r.child.call.n+1)^(e0+E*3) := Nat.pow_le_pow_right (by omega) (by omega)
  have he3 : (r.child.call.n+1)^(E*3)≤(r.child.call.n+1)^(e0+E*3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmeta:=h0 r
  have hb:=envelopeBudget_prefix_bound r
  have hm:=Nat.mul_le_mul_left (K0*((StagePrint.TermsCarrier.word r).length+1)) he0
  have hs:=Nat.mul_le_mul_left ((C+1)^3) he3
  have hsmall:=Nat.mul_le_mul_left (10^7*((StagePrint.TermsCarrier.word r).length+1)) (hp3.trans hs)
  change envelopeBudget r≤_
  nlinarith only [hb,hmeta,hm,hsmall]

end NearQuarticWires.StageCarrierEnvelope
