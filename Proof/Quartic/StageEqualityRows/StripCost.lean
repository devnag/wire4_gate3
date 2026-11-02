import Proof.Quartic.StageEqualityRows.SourceCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StagePrint

/-- `prop:time`, paper/paper.tex: the actual
fourth-field width decoder has a quadratic small-width clock. -/
theorem widthReadSteps_le (r : NativeStreamRequest) : widthReadSteps r≤360*widthScale r^2 := by
  have hw:=bitLength_le (width r)
  have hp:=Control.two_pow_natBitLength_le (width r)
  have hsmall : (width r+1)^2≤widthScale r^2 := Nat.pow_le_pow_left (by unfold widthScale;omega) 2
  unfold widthReadSteps
  calc
    (natBitLength (width r)+2)*(40*2^natBitLength (width r)+40)≤
        (width r+3)*(80*width r+120) :=
      Nat.mul_le_mul (by omega) (by omega)
    _≤360*(width r+1)^2 := by nlinarith
    _≤360*widthScale r^2 := Nat.mul_le_mul_left _ hsmall

/-- `prop:time`, paper/paper.tex: the genuine
column-framing scan is quadratic in the polynomial dense width. -/
theorem columnsSteps_eq (r : NativeStreamRequest) : columnsSteps r=5*(width r)^2+61*width r+22 := by
  have h : (temporaryColumns r).map (fun bits=>5*bits.length+7)=
      (temporaryColumns r).map (fun _=>5*width r+7) := by
    apply List.map_congr_left
    intro bits hb
    rw [temporaryColumns_bitLength r bits hb]
  unfold columnsSteps
  rw [h]
  simp only [List.map_const',List.sum_replicate,temporaryColumns_length]
  ring

theorem bodySteps_le (r : NativeStreamRequest) : bodySteps r≤1000*quadraticScale r := by
  obtain ⟨h1,hA,hB,hAA,hBB,hAB⟩:=scale_bounds r
  have hweak:=weakStream_le r
  have hG:=count_le_stream r
  have hcross : r.cuts.length*(44*width r+55)≤99*(widthScale r*streamScale r) := by
    calc
      r.cuts.length*(44*width r+55)≤ streamScale r*(99*widthScale r) := by
        gcongr <;> first | (unfold streamScale;omega) | (unfold widthScale;omega)
      _=99*(widthScale r*streamScale r) := by ring
  unfold bodySteps weakCountSteps
  have hc : (2*r.cuts.length)*(22*(2*width r+2)+11)=2*(r.cuts.length*(44*width r+55)) := by ring
  rw [hc]
  unfold streamScale at hB
  omega

/-- `prop:time`, paper/paper.tex: physical
header removal, body measurement and complete framed copying cost
at most the same per-walk quadratic stream envelope. -/
theorem stripperSteps_le (r : NativeStreamRequest) : stripperSteps r≤10^7*quadraticScale r := by
  obtain ⟨h1,hA,hB,hAA,hBB,hAB⟩:=scale_bounds r
  have ht:=(temporaryWord_length_le r).trans (stripCapacity_le r)
  have hw:=widthReadSteps_le r
  have hb:=bodySteps_le r
  have hG:=count_le_stream r
  have hn1:=bitLength_le (width r)
  have hn2:=bitLength_le (r.fieldWidth+1)
  have hn3:=bitLength_le (2*r.cuts.length)
  have hcol : columnsSteps r≤100*quadraticScale r := by
    rw [columnsSteps_eq]
    have hsmall : (width r+1)^2≤widthScale r^2 := Nat.pow_le_pow_left (by unfold widthScale;omega) 2
    have hpoly : 5*(width r)^2+61*width r+22≤100*(width r+1)^2 := by nlinarith
    omega
  have hnat : rawNaturalCost (leadingNaturals r)≤1000*quadraticScale r := by
    unfold rawNaturalCost leadingNaturals
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    unfold widthScale at hA
    unfold streamScale at hB
    omega
  unfold stripperSteps
  omega

end NearQuarticWires.StageEqualityRows
