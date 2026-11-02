import Proof.Quartic.StageTupleTermPrice.Steps
import Proof.Quartic.StageTupleTermPrice.Codecs

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: each
actual support selection packet uses the original finite support and
real reverse position, with structural codec lengths only. -/
theorem Step.support_packet_bounds (j : Step) :
    j.supportRequest.support.length+(listWord natWord j.supportRequest.support).length+1≤12*j.small^2 ∧
    j.supportRequest.word.length≤20*j.small^2 ∧
    j.supportRequest.output.length≤2*j.small+3 ∧ supportInputMagnitude j.supportRequest≤20*j.small^2 := by
  have hs:=j.monomial.support_word_length
  have ha : j.monomial.support.length≤j.small := j.monomial.support_length.trans_le j.monomial.card_le_small
  have hi : j.supportRequest.index.val<j.monomial.support.length:=j.supportRequest.index.isLt
  have hnat:=natural_word_length j.supportRequest.index.val
  have hpos:=j.monomial.small_bounds.1
  change 10≤j.small at hpos
  have hatom : j.atom.val≤j.small:=j.atom.isLt.le.trans j.monomial.small_bounds.2.2.2.2.2.1
  have hout : j.supportRequest.output.length≤2*j.small+3 := by
    change (finiteSupportRequest j.monomial.order (reverseSupportIndex j.monomial.order j.done j.done_lt)).output.length≤_
    rw [finiteSupportRequest_output]
    change (natWord j.atom.val).length≤_
    exact (natural_word_length _).trans (by omega)
  change (listWord natWord j.monomial.support).length≤10*j.small^2 at hs
  refine ⟨?_,?_,hout,?_⟩
  · change j.monomial.support.length+(listWord natWord j.monomial.support).length+1≤_
    nlinarith only [hs,ha,hpos]
  · change (natWord j.supportRequest.index.val++listWord natWord j.monomial.support).length≤_
    rw [List.length_append]
    nlinarith only [hs,ha,hi,hnat,hpos]
  · change j.monomial.support.length+j.supportRequest.index.val+
      (listWord natWord j.monomial.support).length+20≤_
    nlinarith only [hs,ha,hi,hpos]

theorem price_supportBudget : Price Step.small (fun j=>j.supportRequest.budget) := by
  obtain ⟨C,E,_hC,_hE,h⟩:=StageTupleCensusBounds.supportIndexCostBound
  refine ⟨C*12^E,2*E,fun j=>?_⟩
  calc
    _≤C*(j.supportRequest.support.length+(listWord natWord j.supportRequest.support).length+1)^E := h j.supportRequest
    _≤C*(12*j.small^2)^E := Nat.mul_le_mul_left C (Nat.pow_le_pow_left j.support_packet_bounds.1 _)
    _=_ := by rw [mul_pow,←pow_mul];ring

/-- `prop:time`, paper/paper.tex: support
input construction, genuine cold selection, output framing and its
actual rewind are paid without a whole-Terms source multiplier. -/
theorem Step.supportPhase_bound (j : Step) :
    supportPhaseCost j.supportRequest≤10^8*j.small^4+1000*j.supportRequest.budget := by
  have hh:=j.support_packet_bounds
  have hs : 1≤j.small:=j.small_pos
  have h2 : j.small^2≤j.small^4:=Nat.pow_le_pow_right hs (by decide)
  have h1 : j.small≤j.small^4:=Nat.le_self_pow (by decide) _
  have h0 : 1≤j.small^4:=Nat.one_le_pow _ _ hs
  have hi:=Nat.pow_le_pow_left hh.2.2.2 2
  unfold supportPhaseCost StagePrint.callAppendCost
  rw [frame_length]
  nlinarith only [hi,hh.2.1,hh.2.2.1,h2,h1,h0]

theorem price_supportPhase : Price Step.small (fun j=>supportPhaseCost j.supportRequest) := by
  have hh:=((Price.constant Step.small (10^8)).mul
    ((Price.scalar (fun j : Step=>le_refl j.small)).pow 4)).add Step.small_pos
    ((Price.constant Step.small 1000).mul price_supportBudget)
  exact hh.mono Step.supportPhase_bound

end NearQuarticWires.StageTupleTermPrice
