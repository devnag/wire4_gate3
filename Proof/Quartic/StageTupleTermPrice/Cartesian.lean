import Proof.Quartic.StageTupleTermPrice.Records
import Proof.Quartic.StageTupleTermPrice.Steps
import Proof.Quartic.StageTupleTermPrice.Weighted

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open StageTuple StagePrint

/-- `prop:time`, paper/paper.tex: the
real Cartesian formatting, current-segment scan, raw reply append and
head return are additive outside the genuine callee clock. -/
def cartesianOverhead (L N M K T : ℕ) : ℕ :=
  3000*(K*N*(2*L+1))+3000*(T*M*(2*L+1))+3000*(N+M+K+T+10)+
    40*(T*M*(2*L+1)+1)+
    400*(2*(K*N*(2*L+1)+1+(T*M*(2*L+1)+1)+N+M+K+T)+11+1)+
    10*(K*T*(N+M)*(2*L+1)+1)+23

theorem cartesian_cost_eq (r : ChildTupleRequest) :
    cartesianStepCost r=cartesianOverhead r.L r.N r.M r.children.length r.tuples.length+
      400*(2*r.budget+2) := by
  unfold cartesianStepCost cartesianInputCost cartesianReplyCost callRecordsCost
  rw [field_records_length _ _ _ r.children_length,field_records_length _ _ _ r.tuples_length,
    child_word_length,tuple_records_length]
  unfold cartesianOverhead
  ring

theorem cartesian_overhead_bound (L N M K T : ℕ) :
    cartesianOverhead L N M K T≤10^8*(L+N+M+1)^4*(K+1)^2*(T+1)^2 := by
  let S:=L+N+M
  have hm : cartesianOverhead L N M K T≤cartesianOverhead S S S K T := by
    unfold cartesianOverhead
    gcongr <;> dsimp only [S] <;> omega
  have hp (S K T : ℕ) : cartesianOverhead S S S K T≤10^8*(S+1)^4*(K+1)^2*(T+1)^2 := by
    unfold cartesianOverhead
    ring_nf
    omega
  exact hm.trans (hp S K T)

/-- `prop:time`, paper/paper.tex: every
actual Cartesian step keeps the original separate quadratic child and
old-tuple factors, including all formatting, call and cleanup clocks. -/
theorem price_cartesianStep : WeightedPrice Step.small Step.square
    (fun j=>cartesianStepCost j.tupleRequest) := by
  obtain ⟨C,E,_hC,_hE,hcost⟩:=StageTupleCensusBounds.childTupleCostBound
  have hsize (j : Step) : j.tupleRequest.L+j.tupleRequest.N+j.tupleRequest.M+1≤4*j.small^2 := by
    have hh:=j.dimensions
    have hs:=j.small_pos
    nlinarith only [hh.1,hh.2.1,hh.2.2,hs]
  have hover : WeightedPrice Step.small Step.square (fun j=>
      cartesianOverhead j.tupleRequest.L j.tupleRequest.N j.tupleRequest.M
        j.tupleRequest.children.length j.tupleRequest.tuples.length) := by
    refine ⟨10^8*4^4,8,fun j=>?_⟩
    calc
      _≤10^8*(j.tupleRequest.L+j.tupleRequest.N+j.tupleRequest.M+1)^4*j.square :=
        by
          simpa only [Step.square,Nat.mul_assoc] using
            cartesian_overhead_bound j.tupleRequest.L j.tupleRequest.N j.tupleRequest.M
              j.tupleRequest.children.length j.tupleRequest.tuples.length
      _≤10^8*(4*j.small^2)^4*j.square :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hsize j) _))
      _=_ := by rw [mul_pow,←pow_mul];ring
  have hbudget : WeightedPrice Step.small Step.square (fun j=>2*j.tupleRequest.budget+2) := by
    refine ⟨C*4^E,2*E,fun j=>?_⟩
    calc
      _≤C*(j.tupleRequest.L+j.tupleRequest.N+j.tupleRequest.M+1)^E*j.square := by simpa only [Step.square,Nat.mul_assoc] using hcost j.tupleRequest
      _≤C*(4*j.small^2)^E*j.square :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hsize j) _))
      _=_ := by rw [mul_pow,←pow_mul];ring
  have hh:=hover.add Step.small_pos (WeightedPrice.mul_small (Price.constant Step.small 400) hbudget)
  exact hh.mono (fun j=>by rw [cartesian_cost_eq])

end NearQuarticWires.StageTupleTermPrice
