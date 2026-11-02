import Proof.Quartic.StageGreedyCollector.CostArithmetic
import Proof.Quartic.StageGreedyContext.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StagePrint

/-- `prop:time`, paper/paper.tex: the
common finite context has polynomial length in original arity,
independently of the entire carrier and the number of repeated walks. -/
theorem contextWord_length_polynomial (B1 B2 : ℕ) : ∃K e : ℕ,
    ∀r : Greedy.PrintRequest B1 B2,(contextWord r).length+1≤K*(r.child.call.n+1)^e := by
  obtain ⟨K,e,hK⟩:=StagePrintContext.contextProducer_polynomial B1 B2
  refine ⟨K*1002^e+4,(B2+8)*e+1,fun r=>?_⟩
  let q:=GreedyCollector.prepared r
  have hb:=StageGreedyContext.context_length_le_budget q
  have hn:=StageMain.CallSize.natWord_le r.child.call.n
  have hc:=StageMain.CallSize.dispatched_callWord_polynomial q.dispatched
  have hp : 1≤(q.call.n+1)^(B2+8):=Nat.one_le_pow _ _ (by omega)
  have hc1 : (callWord q.call).length+1≤1002*(q.call.n+1)^(B2+8) := by omega
  have hctx : (Context.word q).length≤K*1002^e*(q.call.n+1)^((B2+8)*e) := by
    calc
      _≤(StagePrintContext.contextProducer B1 B2).1 q:=hb
      _≤K*((callWord q.call).length+1)^e:=hK q
      _≤K*(1002*(q.call.n+1)^(B2+8))^e:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc1 e)
      _=_:=by rw [mul_pow,←pow_mul];ring
  have hp1 : (q.call.n+1)^((B2+8)*e)≤(q.call.n+1)^((B2+8)*e+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : q.call.n+1≤(q.call.n+1)^((B2+8)*e+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤q.call.n+1)
      (by omega : 1≤(B2+8)*e+1)
  have hctx':=hctx.trans (Nat.mul_le_mul_left (K*1002^e) hp1)
  change (natWord q.call.n++Context.word q).length+1≤_
  simp only [List.length_append]
  change (natWord q.call.n).length≤2*q.call.n+3 at hn
  change _≤(K*1002^e+4)*(q.call.n+1)^((B2+8)*e+1)
  nlinarith only [hn,hctx',hp2]

/-- `prop:time`, paper/paper.tex: copying
the genuinely finite context once per original walk still fits one
outer-column budget, with no whole-carrier rescan per entry. -/
theorem repeated_context_selected (B1 B2 : ℕ) :
    SelectedBudget (B1:=B1) (B2:=B2)
      (fun r=>(entryCalls r).length*((contextWord r).length+1)) := by
  obtain ⟨K,e,hK⟩:=contextWord_length_polynomial B1 B2
  refine ⟨K,e,fun r=>?_⟩
  have hn:=StageLiftSourceCost.walkCount_le_columns r
  have hh:=Nat.mul_le_mul hn (hK r)
  simpa only [entryCalls,List.length_ofFn,Nat.mul_left_comm,Nat.mul_assoc] using hh

end NearQuarticWires.StageGreedyCollector
