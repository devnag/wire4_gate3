import Proof.Gates.WordPrograms.Hoare

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: a counted
Terms loop pays each actual monomial clock once, plus its literal
decrement, sequencing and loop-test transitions. -/
def countedSourceCost (cost : ℕ→ℕ) : ℕ→ℕ→ℕ
  | _,0 => 1
  | start,passes+1 => cost start+4+countedSourceCost cost (start+1) passes

/-- `lem:print` and `prop:time`, paper/paper.tex: variable-cost counted execution adds genuine body
costs instead of multiplying a maximum monomial count by a maximum
child-choice census. The fixed actual loop body is unchanged. -/
theorem countedSource_run {ns nr cap : ℕ} {K : Fin nr} {body : WMX ns nr}
    (cost : ℕ→ℕ) (n : ℕ) (Inv : ℕ→WState ns nr→Prop) (hcap : n ≤ cap)
    (hstep : ∀k<n,∀σ,Inv k σ→σ.val K=n-k→
      Runs cap body (σ.setv K (n-k-1)) (cost k)
        (fun τ=>Inv (k+1) τ ∧ τ.val K=n-k-1)) :
    ∀σ,Inv 0 σ→σ.val K=n→
      Runs cap (.whr K (.seq (.wm (.dec K)) body)) σ (countedSourceCost cost 0 n)
        (fun τ=>Inv n τ ∧ τ.val K=0) := by
  have key : ∀m j σ,j+m=n→Inv j σ→σ.val K=n-j→
      Runs cap (.whr K (.seq (.wm (.dec K)) body)) σ (countedSourceCost cost j m)
        (fun τ=>Inv n τ ∧ τ.val K=0) := by
    intro m
    induction m with
    | zero =>
      intro j σ hj hI hK
      rw [Nat.add_zero] at hj
      subst j
      exact ⟨σ,WXExec.whrF (by omega),hI,by omega⟩
    | succ m ih =>
      intro j σ hj hI hK
      have hd := WXExec.dec cap K σ (by omega)
      rw [hK] at hd
      obtain ⟨a,ea,ha,hKa⟩ := hstep j (by omega) σ hI hK
      obtain ⟨b,eb,hb⟩ := ih (j+1) a (by omega) ha (by omega)
      exact ⟨b,(WXExec.whrT (by omega) (hd.seq ea) eb).mono
        (by simp only [countedSourceCost];omega),hb⟩
  intro σ hI hK
  exact key n 0 σ (by omega) hI (by omega)

/-- `prop:time`, paper/paper.tex: the literal
variable-cost clock is the sum of its actual monomial stage costs and
four transitions per monomial, with one final loop test. -/
theorem countedSourceCost_eq_sum (cost : ℕ→ℕ) (start passes : ℕ) :
    countedSourceCost cost start passes=
      ((List.range' start passes).map cost).sum+4*passes+1 := by
  induction passes generalizing start with
  | zero => simp [countedSourceCost]
  | succ passes ih =>
    simp only [countedSourceCost,List.range'_succ,List.map_cons,List.sum_cons,ih]
    omega

end NearQuarticWires.StageTuple
