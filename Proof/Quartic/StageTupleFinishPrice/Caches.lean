import Proof.Quartic.StageTupleFinishPrice.Data

set_option autoImplicit false

namespace NearQuarticWires.StageTupleFinishPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StageTuple StageTupleTermPrice

/-- `prop:time`, paper/paper.tex: the exact
three finite finish caches contain the actual support packet and
signed coefficient source/reply, independently of prior output/history. -/
def cacheSize (j : Case) : ℕ :=
  let data:=j.request.progressMonomial j.index j.index_lt
  ((data.reverseData j.request data.order.length).caches 0).length+
    ((data.reverseData j.request data.order.length).caches 1).length+
    ((data.reverseData j.request data.order.length).caches 2).length+10

/-- `prop:time`, paper/paper.tex: literal cache
bytes are exactly the original support word, one framed binary signed
coefficient source and its fixed-width double-framed reply. -/
theorem cacheSize_eq (j : Case) : cacheSize j=
    (frame (listWord natWord j.support)).length+
    (frame (CoefficientRequest.word ⟨j.width,j.term.2⟩)).length+
    (CoefficientRequest.output ⟨j.width,j.term.2⟩).length+10 := rfl

/-- `prop:time`, paper/paper.tex: current
support and coefficient cache sizes are polynomial in the original
structural magnitude, including zero and negative coefficients. -/
theorem cacheSize_le (j : Case) : cacheSize j≤100*j.small^2 := by
  have hs:=j.support_word_length
  have hc:=j.coefficient_word_length
  have hw:=j.small_bounds.2.2.1
  have hn:=natural_word_length j.width
  have hp:=j.small_pos
  have hsq : j.small≤j.small^2:=Nat.le_self_pow (by decide) _
  have h0 : (frame (listWord natWord j.support)).length≤20*j.small^2+1 := by
    rw [frame_length]
    omega
  have h1 : (frame (CoefficientRequest.word ⟨j.width,j.term.2⟩)).length≤24*j.small+7 := by
    simp only [frame_length,CoefficientRequest.word,List.length_append]
    omega
  have h2 : (CoefficientRequest.output ⟨j.width,j.term.2⟩).length≤4*j.small+3 := by
    simp only [CoefficientRequest.output,frame_length,SignedSortKey.binary_length]
    omega
  rw [cacheSize_eq]
  nlinarith only [h0,h1,h2,hsq,hp]

/-- `prop:time`, paper/paper.tex: finite cache
erasure is absorbed into the unchanged square census without adding
an exponent or any earlier Terms/history factor. -/
theorem caches_selected (j : Case) : cacheSize j≤100*j.small^4*j.childCap^(2*j.card) := by
  have hs:=Nat.pow_le_pow_right j.small_pos (show 2≤4 by decide)
  have hp : 1≤j.childCap^(2*j.card):=Nat.one_le_pow _ _ j.childCap_pos
  calc
    _≤100*j.small^2:=cacheSize_le j
    _≤100*j.small^4:=Nat.mul_le_mul_left 100 hs
    _≤100*j.small^4*j.childCap^(2*j.card):=by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (100*j.small^4) hp

end NearQuarticWires.StageTupleFinishPrice
