import Proof.Quartic.StageEqualityRows.Stripper
import Proof.Quartic.StageEqualityRows.SharpCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open StagePrint StagePrint.Downstream

def widthScale (r : NativeStreamRequest) : ℕ := width r+r.fieldWidth+2
def streamScale (r : NativeStreamRequest) : ℕ := (stream r).length+1

def quadraticScale (r : NativeStreamRequest) : ℕ := widthScale r^2*streamScale r^2

/-- `prop:time`, paper/paper.tex: all small
source widths and actual stream lengths are controlled separately. -/
theorem scale_bounds (r : NativeStreamRequest) :
    1≤quadraticScale r ∧ widthScale r≤quadraticScale r ∧ streamScale r≤quadraticScale r ∧
    widthScale r^2≤quadraticScale r ∧ streamScale r^2≤quadraticScale r ∧
    widthScale r*streamScale r≤quadraticScale r := by
  let A:=widthScale r
  let B:=streamScale r
  have ha : 1≤A := by dsimp [A,widthScale];omega
  have hb : 1≤B := by dsimp [B,streamScale];omega
  have ha2 : 1≤A^2 := Nat.one_le_pow _ _ ha
  have hb2 : 1≤B^2 := Nat.one_le_pow _ _ hb
  have hA : A^2≤A^2*B^2 := by simpa using Nat.mul_le_mul_left (A^2) hb2
  have hB : B^2≤A^2*B^2 := by simpa using Nat.mul_le_mul_right (B^2) ha2
  have hAB : A*B≤A^2*B^2 := by nlinarith only [Nat.le_mul_self (A*B)]
  change 1≤A^2*B^2 ∧ A≤A^2*B^2 ∧ B≤A^2*B^2 ∧
    A^2≤A^2*B^2 ∧ B^2≤A^2*B^2 ∧ A*B≤A^2*B^2
  exact ⟨Nat.mul_pos ha2 hb2,(by nlinarith only [hA,Nat.le_mul_self A]),
    (by nlinarith only [hB,Nat.le_mul_self B]),hA,hB,hAB⟩

theorem input_length (r : NativeStreamRequest) :
    (equalityRowsInput r).length=2*(stream r).length+2*width r+2*r.fieldWidth+11 := by
  simp [equalityRowsInput,Top.loadRec,frame_length,stream,width]
  ring

theorem loadCost_eq (r : NativeStreamRequest) :
    loadCost r=12*(stream r).length+12*width r+12*r.fieldWidth+93 := by
  unfold loadCost Top.loadCost Top.loadChainCost
  change 2*(2*(equalityRowsInput r).length+1)+2+1+
    (2*(_)+2)=_
  rw [input_length]
  simp only [List.length_replicate,List.length_nil]
  ring

theorem stripCapacity_le (r : NativeStreamRequest) : stripCapacity r≤1000*quadraticScale r := by
  have h:=scale_bounds r
  have hg:=count_le_stream r
  have hw : width r+1≤widthScale r := by unfold widthScale;omega
  have hw2 : (width r+1)^2≤widthScale r^2 := Nat.pow_le_pow_left hw 2
  have hwidth : width r≤quadraticScale r := by unfold widthScale at h;omega
  have hfield : r.fieldWidth≤quadraticScale r := by unfold widthScale at h;omega
  have hstream : (stream r).length≤quadraticScale r := by unfold streamScale at h;omega
  unfold stripCapacity capacity loadCapacity
  change 2*(equalityRowsInput r).length+1+
    Top.loadChainCost (stream r) (List.replicate (width r) true)
      (List.replicate r.fieldWidth true) [] [] [] [] [] [] [] []+
    100*(stream r).length+100*(width r+r.fieldWidth+r.cuts.length+1)+100+100*(width r+1)^2≤_
  rw [input_length]
  unfold Top.loadChainCost
  simp only [List.length_replicate,List.length_nil]
  omega

end NearQuarticWires.StageEqualityRows
