import Proof.Quartic.StagePrintContext.Program
import Proof.Quartic.StageCertTests.ParameterReadCost

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCertTests StageFormulaMetadata StageMain.Compact StagePrint.Header

/-- `prop:time`, paper/paper.tex: both real
source scans and the complete parameter decoder have cubic cost in
the measured finite preparation, uniformly over original witnesses. -/
theorem readSteps_bound {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    readSteps r≤1000000*(r.word.length+1)^3 := by
  let A:=r.word.length+1
  have hA : 1≤A := by dsimp [A];omega
  have hcall : (callWord r.call).length+1≤A := Nat.add_le_add_right (call_length_le r) 1
  have hpar : (Program.parametersWord r.selected.1).length+1≤A :=
    Nat.add_le_add_right (parameter_length_le r) 1
  have hwit : (Program.witnessPrefix r.call r.selected.1 r.witness).length≤A := by
    have hh:=witness_length_le r
    dsimp [A]
    omega
  have hword : compactInput r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)=r.word :=
    (prepWord_eq_compact r.dispatched r.witness).symm
  have hpre : (StageLift.preparedPrefixWord r.call r.selected.1).length≤A := by
    have hh:=congrArg List.length hword
    simp only [compactInput,List.length_append] at hh
    dsimp [A]
    omega
  have hreader:=parameterReadCost_le_word r.selected.1 r.word.length
  have hreader' : StageLift.parameterReadCost r.selected.1 r.word.length≤5000*A^2 := by
    have hh:=Nat.mul_le_mul_right A (Nat.mul_le_mul_left 5000 hpar)
    change 5000*((Program.parametersWord r.selected.1).length+1)*A≤5000*A*A at hh
    change StageLift.parameterReadCost r.selected.1 r.word.length≤5000*A^2
    change StageLift.parameterReadCost r.selected.1 r.word.length≤
      5000*((Program.parametersWord r.selected.1).length+1)*A at hreader
    nlinarith
  have hcube:=Nat.pow_le_pow_left hcall 3
  have hsquare:=Nat.pow_le_pow_left hpar 2
  have hA2 : A≤A^2 := by nlinarith
  have hA3 : A^2≤A^3 := by nlinarith
  change readSteps r≤1000000*A^3
  unfold readSteps initializeCost acquireCost decodeCost
  rw [hword]
  dsimp only [A] at hA2 hA3 ⊢
  dsimp only [A] at hA hcall hpar hwit hpre hreader' hcube hsquare
  nlinarith only [hA,hcall,hpar,hwit,hpre,hreader',hcube,hsquare,hA2,hA3]

/-- `prop:time`, paper/paper.tex: the actual
translation is computed by a finite witness-prefix loop, and its
numeric syndrome value never appears as a running-time factor. -/
theorem baseHeaderCost_bound {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    baseHeaderCost r.call r.selected.1 r.witness≤10000*(r.word.length+1)^2 := by
  let A:=r.word.length+1
  have hA : 1≤A := by dsimp [A];omega
  have hn : r.call.n≤A := by have hh:=arity_le_source r;dsimp [A];omega
  have hk : r.selected.1.k≤A := by
    have hh:=(Cells.prepare_spec _ r.selected.1 r.selected.2).k_lt_n
    change r.selected.1.k<r.call.n at hh
    omega
  have hw : (Program.witnessPrefix r.call r.selected.1 r.witness).length≤A := by
    have hh:=witness_length_le r;dsimp [A];omega
  have hc : (callWord r.call).length≤A := by have hh:=call_length_le r;dsimp [A];omega
  have hbits : natBitLength r.call.n≤A+1 :=
    (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (by omega)
  have hsize : Nat.size r.call.n≤A := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hn
  have ht:=Nat.mul_le_mul hk (show
    (Program.witnessPrefix r.call r.selected.1 r.witness).length+6*r.selected.1.k+21≤7*A+21 by omega)
  change baseHeaderCost r.call r.selected.1 r.witness≤10000*A^2
  unfold baseHeaderCost translationCost
  nlinarith only [hA,hn,hk,hw,hc,hbits,hsize,ht]

/-- `prop:time`, paper/paper.tex: the whole
common context is emitted with quadratic source cost in its actual
finite input, including every nested frame and delimiter. -/
theorem bodySteps_bound {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    bodySteps r (finiteWidth r.word.length)≤10000000*(r.word.length+1)^2 := by
  have hcall:=call_length_le r
  have hhead:=baseHeaderCost_bound r
  unfold bodySteps headerFieldCost countsFieldCost fieldClock finiteWidth StagePrint.Context.header
  nlinarith

/-- `prop:time`, paper/paper.tex: cold source
acquisition and complete context framing have cubic measured-input cost. -/
theorem contextSteps_bound {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    contextSteps r≤100000000*(r.word.length+1)^3 := by
  have hr:=readSteps_bound r
  have hb:=bodySteps_bound r
  have hq : (r.word.length+1)^2≤(r.word.length+1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide : 2≤3)
  have hp : 1≤(r.word.length+1)^3 := Nat.pow_pos (by omega)
  unfold contextSteps
  omega

end NearQuarticWires.StagePrintContext
