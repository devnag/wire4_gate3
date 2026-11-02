import Proof.Quartic.StageEqualityRows.CostBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StagePrint

/-- `prop:time`, paper/paper.tex: the counted
original-row source has its actual three binary metadata fields and
single unchanged equality stream. -/
theorem source_length_le (r : NativeStreamRequest) :
    r.equalitySource.length≤20*quadraticScale r := by
  obtain ⟨h1,hA,hB,hAA,hBB,hAB⟩:=scale_bounds r
  have hw:=bitLength_le (width r)
  have hp:=bitLength_le r.fieldWidth
  have hg:=bitLength_le r.cuts.length
  have hG:=count_le_stream r
  unfold widthScale at hA
  unfold streamScale at hB
  unfold NativeStreamRequest.equalitySource EquationRowRaw.source EquationHeaderRead.word
    EquationHeaderRead.header NativeStreamRequest.equalityInput EquationRowCuts.stream
  simp only [List.length_append,List.length_cons,NearCubicGates.Close.CounterAsm.natWord_len]
  change (2*natBitLength (width r)+1)+(2*natBitLength r.fieldWidth+1)+
    (2*natBitLength r.cuts.length+1)+((stream r).length+1)≤_
  omega

/-- `prop:time`, paper/paper.tex: use the
literal constructor clock, whose census dependence is quadratic
within one walk, instead of its coarser cubic uniform envelope. -/
theorem equalityBudget_le (r : NativeStreamRequest) :
    r.equalityBudget≤10^7*quadraticScale r := by
  have hsource:=source_length_le r
  have hraw:=raw_budget_quadratic r.equalityInput
  have hcount:=count_le_stream r
  have hp : (r.cuts.length+1)^2≤ streamScale r^2 :=
    Nat.pow_le_pow_left (by unfold streamScale;omega) 2
  have hmain : 10^6*widthScale r^2*(r.cuts.length+1)^2≤10^6*quadraticScale r := by
    have h:=Nat.mul_le_mul_left (10^6*widthScale r^2) hp
    simpa only [quadraticScale,Nat.mul_assoc] using h
  change EquationRowRaw.budget r.equalityInput≤10^6*widthScale r^2*(r.cuts.length+1)^2+
    4*r.equalitySource.length at hraw
  have h1:1≤quadraticScale r:=(scale_bounds r).1
  unfold NativeStreamRequest.equalityBudget EquationRowFramed.budget
  omega

theorem naturalCost_le (n : ℕ) : naturalCost n≤3300*(n+1)^2 := by
  have hn:=bitLength_le n
  unfold naturalCost
  calc
    (natBitLength n+10)*(100*n+200)≤(n+11)*(100*n+200) := Nat.mul_le_mul_right _ (by omega)
    _≤3300*(n+1)^2 := by nlinarith

/-- `prop:time`, paper/paper.tex: count-based
metadata writing is quadratic in this one stream's census only. -/
theorem formatterSteps_le (r : NativeStreamRequest) : formatterSteps r≤10^5*quadraticScale r := by
  obtain ⟨h1,hA,hB,hAA,hBB,hAB⟩:=scale_bounds r
  have hw:=naturalCost_le (width r)
  have hp:=naturalCost_le r.fieldWidth
  have hg:=naturalCost_le r.cuts.length
  have hG:=count_le_stream r
  have hw2 : (width r+1)^2≤widthScale r^2 := Nat.pow_le_pow_left (by unfold widthScale;omega) 2
  have hp2 : (r.fieldWidth+1)^2≤widthScale r^2 := Nat.pow_le_pow_left (by unfold widthScale;omega) 2
  have hg2 : (r.cuts.length+1)^2≤ streamScale r^2 := Nat.pow_le_pow_left (by unfold streamScale;omega) 2
  have hcross : r.cuts.length*(44*width r+55)≤99*(widthScale r*streamScale r) := by
    calc
      r.cuts.length*(44*width r+55)≤ streamScale r*(99*widthScale r) := by
        gcongr <;> first | (unfold streamScale;omega) | (unfold widthScale;omega)
      _=99*(widthScale r*streamScale r) := by ring
  rw [show formatterSteps r=loadCost r+(16*width r+14)+(16*r.fieldWidth+14)+(36*width r+16)+
      countCost r+(23*(stream r).length+6)+
      (naturalCost (width r)+naturalCost r.fieldWidth+naturalCost r.cuts.length+2)+
      (22*(stream r).length+26)+20 from rfl,loadCost_eq]
  unfold countCost
  unfold widthScale at hA
  unfold streamScale at hB
  have hc : r.cuts.length*(22*(2*width r+2)+11)=r.cuts.length*(44*width r+55) := by ring
  rw [hc]
  omega

end NearQuarticWires.StageEqualityRows
