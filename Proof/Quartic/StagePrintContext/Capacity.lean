import Proof.Quartic.StagePrintContext.Acquire
import Proof.Quartic.StageFormulaMetadata.FiniteMachine

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCertTests StageMain.Compact StageFormulaMetadata

/-- `prop:time`, paper/paper.tex: the literal
original call remains inside the physically read finite preparation. -/
theorem call_length_le {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    (callWord r.call).length≤r.word.length := by
  rw [PreparedScheduleRequest.word,prepWord_eq_compact r.dispatched]
  simp only [compactInput,StageLift.preparedPrefixWord,List.length_cons,List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: dispatch
bounds original arity by the actual source bytes, not by a new input field. -/
theorem arity_le_source {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    r.call.n≤r.word.length :=
  (Cells.dispatched_n_le_callWord r.dispatched).trans (call_length_le r)

/-- `prop:time`, paper/paper.tex: all public
parameter bytes are part of the actual finite preparation source. -/
theorem parameter_length_le {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    (Program.parametersWord r.selected.1).length≤r.word.length := by
  rw [PreparedScheduleRequest.word,prepWord_eq_compact r.dispatched]
  simp only [compactInput,StageLift.preparedPrefixWord,List.length_cons,List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: only the
algorithm's finite zero-padded witness prefix is retained and charged. -/
theorem witness_length_le {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    (Program.witnessPrefix r.call r.selected.1 r.witness).length≤r.word.length := by
  rw [PreparedScheduleRequest.word,prepWord_eq_compact r.dispatched]
  simp only [compactInput,StageLift.preparedPrefixWord,List.length_cons,List.length_append,frame_length]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actually measured finite source width covers all
compact parsing and original affine-header arithmetic, uniformly over
proposed witnesses, without a supplied workspace-size field. -/
theorem context_capacity {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    r.word.length+2≤finiteWidth r.word.length ∧
    r.call.n+3≤finiteWidth r.word.length ∧
    4*(r.call.n+1)^2+r.call.n+20<2^finiteWidth r.word.length := by
  have hn:=arity_le_source r
  have hbase : r.call.n+1≤2^(r.call.n+1) := Nat.lt_two_pow_self.le
  have hsquare : (r.call.n+1)^2≤2^(2*(r.call.n+1)) := by
    have hh:=Nat.pow_le_pow_left hbase 2
    simpa only [←pow_mul,Nat.mul_comm] using hh
  have hpower : 2^(2*(r.call.n+1)+5)<2^finiteWidth r.word.length :=
    Nat.pow_lt_pow_right (by decide) (by unfold finiteWidth;omega)
  refine ⟨by unfold finiteWidth;omega,by unfold finiteWidth;omega,?_⟩
  calc
    4*(r.call.n+1)^2+r.call.n+20≤32*(r.call.n+1)^2 := by nlinarith
    _≤32*2^(2*(r.call.n+1)) := Nat.mul_le_mul_left _ hsquare
    _=2^(2*(r.call.n+1)+5) := by rw [pow_add];norm_num;omega
    _<2^finiteWidth r.word.length := hpower

end NearQuarticWires.StagePrintContext
