import Proof.Quartic.StageGreedyContext.Machine
import Proof.Quartic.StageGreedyContext.SmallCosts

/-!
# The actual one-context budget is linear in the complete carrier length

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the
actual ordinary frontend budget is a fixed polynomial in original
arity times the actual carrier length, never a square of that carrier
or a numeric walk count or entry index. -/
theorem actualBudget_bound (B1 B2 : ℕ) :
    StageGreedyCollector.ContextBudgetBound (B1:=B1) (B2:=B2) (fun r=>(actualRequest r).budget) := by
  obtain ⟨K,e,hK⟩:=finiteWork_polynomial B1 B2
  let A:=K*1002^e
  let degree:=(B2+8)*e
  refine ⟨2*A+402,degree,fun r=>?_⟩
  let q:=StagePrint.GreedyCollector.prepared r
  let t:=actualRequest r
  let Y:=(r.child.call.n+1)^degree
  let L:=(StagePrint.TermsCarrier.word r).length
  have hcall:=StageMain.CallSize.dispatched_callWord_polynomial q.dispatched
  have hp : 1≤(q.call.n+1)^(B2+8):=Nat.one_le_pow _ _ (by omega)
  have hcallOne : (callWord q.call).length+1≤1002*(q.call.n+1)^(B2+8) := by
    have grow (x y : ℕ) (hy : 1≤y) (hx : x≤1001*y) : x+1≤1002*y := by omega
    exact grow _ _ hp hcall
  have hwork : finiteWork q≤A*Y := by
    calc
      _≤K*((callWord q.call).length+1)^e:=hK q
      _≤K*(1002*(q.call.n+1)^(B2+8))^e:=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcallOne e)
      _=A*Y:=by
        rw [mul_pow,←pow_mul]
        change K*(1002^e*Y)=K*1002^e*Y
        exact (Nat.mul_assoc K (1002^e) Y).symm
  have hsource:=sourceSteps_bound t
  have hsuffix : t.suffix.length≤L :=
    t.suffix_length_le.trans_eq (congrArg List.length (actualRequest_word r))
  have hS : t.sourceSteps≤A*Y+200*L :=
    hsource.trans (Nat.add_le_add hwork (Nat.mul_le_mul_left _ hsuffix))
  have hY : 1≤Y:=Nat.one_le_pow _ _ (by omega)
  have hfirst : Y≤Y*(L+1):=Nat.le_mul_of_pos_right _ (by omega)
  have hsecond : L+1≤Y*(L+1):=Nat.le_mul_of_pos_left _ hY
  change t.budget≤(2*A+402)*Y*(L+1)
  calc
    t.budget=2*t.sourceSteps+2:=rfl
    _≤2*(A*Y+200*L)+2:=Nat.add_le_add_right (Nat.mul_le_mul_left _ hS) _
    _=2*A*Y+(400*L+2):=by ring
    _≤2*A*(Y*(L+1))+402*(Y*(L+1)):=Nat.add_le_add
      (Nat.mul_le_mul_left _ hfirst)
      ((show 400*L+2≤402*(L+1) by omega).trans (Nat.mul_le_mul_left _ hsecond))
    _=(2*A+402)*Y*(L+1):=by ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the SAME actual compiled budget
of the complete context producer satisfies the frozen linear-carrier
interface, with no additional source or machine hypothesis. -/
theorem contextProducer_bound (B1 B2 : ℕ) :
    StageGreedyCollector.ContextBudgetBound (contextProducer B1 B2).1 := by
  exact actualBudget_bound B1 B2

end NearQuarticWires.StageGreedyContext
