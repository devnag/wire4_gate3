import Proof.Quartic.StageEntryAllocation.Width
import Proof.Quartic.StageMain.CompilerRuntime

set_option autoImplicit false

namespace NearQuarticWires.StageEntryAllocation

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePrint.EntryFormat

/-- `prop:time`, paper/paper.tex: all fixed
compiler dimensions and actual initialized arithmetic dimensions share
one small original-arity scale, independent of payload and execution length. -/
def scale (C E n : ℕ) : ℕ :=
  (sizes C E).W (natBitLength n)+10*(C+1)+(E+2)+VV+MM+n+1000

/-- `prop:time`, paper/paper.tex: the fixed
coefficient of that scale depends only on the chosen sizing polynomial. -/
def coefficient (C E : ℕ) : ℕ :=
  10*(C+1)*2^(E+2)+10*(C+1)+(E+2)+VV+MM+1001

/-- `prop:time`, paper/paper.tex: the actual
finite setup and compiler dimensions remain polynomial in original arity. -/
theorem scale_polynomial (C E n : ℕ) :
    scale C E n≤coefficient C E*(n+1)^(E+3) := by
  have hW:=width_polynomial C E n
  have hbase : 1≤n+1 := by omega
  have hp : (n+1)^(E+2)≤(n+1)^(E+3) := Nat.pow_le_pow_right hbase (by omega)
  have hw:=hW.trans (Nat.mul_le_mul_left _ hp)
  have hone : 1≤(n+1)^(E+3) := Nat.one_le_pow _ _ hbase
  have hn : n≤(n+1)^(E+3) := (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
  have hconstant : 10*(C+1)+(E+2)+VV+MM+1000≤
      (10*(C+1)+(E+2)+VV+MM+1000)*(n+1)^(E+3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold scale coefficient
  nlinarith only [hw,hn,hconstant]

/-- `prop:time`, paper/paper.tex: this is the
bound for the actual same-size Cells setup, compiled execution and
teardown, with input bytes and source steps occurring only linearly. -/
theorem actual_langBudget_bound (C E : ℕ) (modular : Bool)
    (r : BoundedRequest C E modular) (steps : ℕ) :
    langBudget StageRecovery.packetCallee (sizes C E) VV MM r.word steps≤
      10000*(scale C E r.header.call.n)^2*(steps+r.word.length+1) := by
  apply StageMain.Runtime.langBudget_le
  · unfold scale;omega
  · unfold scale;omega
  · unfold scale;omega
  · change 3≤ scale C E r.header.call.n
    unfold scale;omega
  · change 10*(C+1)≤ scale C E r.header.call.n
    unfold scale;omega
  · change E+2≤ scale C E r.header.call.n
    unfold scale;omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rw [original_header]
    have h:=NearCubicGates.Close.Dispatch.natBitLength_le_succ r.header.call.n
    unfold scale
    omega
  · rw [original_header]
    unfold scale
    omega
  · simp only [sizes,Sz.Lk,Nat.mul_zero]
    exact Nat.zero_le _
  · simp only [sizes,Sz.Bk,Nat.mul_zero]
    exact Nat.zero_le _

/-- `prop:time`, paper/paper.tex: arbitrary
actual formatter executions have linear total source and execution
cost times a fixed polynomial of the original arity in both modes. -/
theorem linear_budget (C E : ℕ) (modular : Bool) : ∃K e : ℕ,
    ∀(r : BoundedRequest C E modular)(steps : ℕ),
      langBudget StageRecovery.packetCallee (sizes C E) VV MM r.word steps≤
        K*(r.word.length+steps+1)*(r.header.call.n+1)^e := by
  refine ⟨10000*(coefficient C E)^2,(E+3)*2,fun r steps=>?_⟩
  calc
    _≤10000*(scale C E r.header.call.n)^2*(steps+r.word.length+1) :=
      actual_langBudget_bound C E modular r steps
    _≤10000*(coefficient C E*(r.header.call.n+1)^(E+3))^2*(steps+r.word.length+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (scale_polynomial C E r.header.call.n) _))
    _=_ := by rw [mul_pow,←pow_mul];ring

end NearQuarticWires.StageEntryAllocation
