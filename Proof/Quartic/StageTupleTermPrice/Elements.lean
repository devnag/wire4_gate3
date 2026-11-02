import Proof.Quartic.StageTupleTermPrice.Steps

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

/-- `prop:time`, paper/paper.tex: original
child counts, suffix tuple counts and their product are each paid
inside the same separate actual child/tuple square. -/
theorem Step.square_elements (j : Step) :
    j.tupleRequest.children.length≤j.square ∧ j.tupleRequest.tuples.length≤j.square ∧
    j.tupleRequest.children.length*j.tupleRequest.tuples.length≤j.square ∧
    (j.tupleRequest.children.length+1)^2≤j.square := by
  let K:=j.tupleRequest.children.length
  let T:=j.tupleRequest.tuples.length
  have hpK : K+1≤(K+1)^2:=Nat.le_self_pow (by decide) _
  have hpT : T+1≤(T+1)^2:=Nat.le_self_pow (by decide) _
  have hprod:=Nat.mul_le_mul hpK hpT
  have hK:=Nat.le_mul_of_pos_right ((K+1)^2) (by positivity : 0<(T+1)^2)
  have hT:=Nat.le_mul_of_pos_left ((T+1)^2) (by positivity : 0<(K+1)^2)
  have hKT:=Nat.mul_le_mul (Nat.le_succ K) (Nat.le_succ T)
  change K≤(K+1)^2*(T+1)^2 ∧ T≤(K+1)^2*(T+1)^2 ∧
    K*T≤(K+1)^2*(T+1)^2 ∧ (K+1)^2≤(K+1)^2*(T+1)^2
  exact ⟨(Nat.le_succ _).trans (hpK.trans hK),(Nat.le_succ _).trans (hpT.trans hT),hKT.trans hprod,hK⟩

end NearQuarticWires.StageTupleTermPrice
