import Proof.Quartic.StageTupleTermPrice.Acquire

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary_length)
open NearCubicGates.Close.Interfaces
open StageTuple

def Case.coefficientRequest (j : Case) : CoefficientRequest:=⟨j.width,j.term.2⟩

/-- `prop:time`, paper/paper.tex: the
actual signed coefficient converter is priced solely from its own
width and canonical coefficient packet, including all cold framing. -/
theorem price_coefficientBudget : Price Case.small (fun j=> j.coefficientRequest.budget) := by
  obtain ⟨C,E,_hC,_hE,h⟩:=StageTupleCensusBounds.coefficientCostBound
  refine ⟨C*12^E,E,fun j=>?_⟩
  have hw:=j.small_bounds.2.2.1
  have hc:=j.coefficient_word_length
  have hp:=j.small_pos
  have hs : j.width+(intWord j.term.2).length+1≤12*j.small := by omega
  calc
    _≤ C*(j.width+(intWord j.term.2).length+1)^E := h j.coefficientRequest
    _≤ C*(12*j.small)^E := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs _)
    _=_ := by rw [mul_pow];ring

/-- `prop:time`, paper/paper.tex: actual
support measurement/counting and coefficient-call/copy/rewind costs
are additive and exclude the complete Terms count and history. -/
theorem Case.prepare_bound (j : Case) :
    monomialPrepareCost j.width j.support j.term.2≤
      100000*j.small^2+1000*j.coefficientRequest.budget := by
  have hs:=j.support_word_length
  have ha : j.support.length≤ j.small := j.support_length.trans_le j.card_le_small
  have hw:=j.small_bounds.2.2.1
  have hc:=j.coefficient_word_length
  have hn:=natural_word_length j.width
  have hr:=natural_count_readCost_le j.support.length
  have hpos:=j.small_bounds.1
  unfold monomialPrepareCost cachedCallCost StagePrint.callAppendCost scalarReadCost
  simp only [CoefficientRequest.word,CoefficientRequest.output,frame_length,binary_length,List.length_append]
  change _≤100000*j.small^2+1000*(CoefficientRequest.mk j.width j.term.2).budget
  nlinarith only [hs,ha,hw,hc,hn,hr,hpos]

theorem price_prepare : Price Case.small (fun j=>
    monomialPrepareCost j.width j.support j.term.2) := by
  have hh:=((Price.constant Case.small 100000).mul
    ((Price.scalar (fun j : Case=> le_refl j.small)).pow 2)).add Case.small_pos
    ((Price.constant Case.small 1000).mul price_coefficientBudget)
  exact hh.mono Case.prepare_bound

end NearQuarticWires.StageTupleTermPrice
