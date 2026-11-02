import Proof.Quartic.StageTupleSetupCold.Budget
import Proof.Quartic.StageTupleSetup.CoefficientCost

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCost

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: every
small setup input is bounded by the original structural magnitude,
which excludes the complete Terms list and its length. -/
structure StructuralBounds (r : TermCutRequest) : Prop where
  ten : 10 ≤ r.setupStructuralMagnitude
  width : r.stackWidth+1 ≤ r.setupStructuralMagnitude
  arity : r.header.call.n ≤ r.setupStructuralMagnitude
  header : ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord).length ≤ r.setupStructuralMagnitude
  context : r.contextWord.length ≤ r.setupStructuralMagnitude
  degree : (natWord r.degree).length ≤ r.setupStructuralMagnitude

theorem structural_bounds (r : TermCutRequest) : StructuralBounds r := by
  constructor <;> unfold TermCutRequest.setupStructuralMagnitude <;> omega

theorem fixed_integer_bytes : (intWord (0 : ℤ)).length=6 ∧ (intWord (1 : ℤ)).length=6 := by decide

/-- `prop:time`, paper/paper.tex: both
width codecs and the fixed zero/one coefficient packets fit the small
structural magnitude without referring to any Terms bytes or hint. -/
theorem small_bytes (r : TermCutRequest) :
    (natWord r.stackWidth).length ≤ 3*r.setupStructuralMagnitude ∧
    (natWord (r.stackWidth+1)).length ≤ 3*r.setupStructuralMagnitude ∧
    (natWord (r.stackWidth+1)++intWord (0 : ℤ)).length ≤ 4*r.setupStructuralMagnitude ∧
    (natWord (r.stackWidth+1)++intWord (1 : ℤ)).length ≤ 4*r.setupStructuralMagnitude := by
  have hs:=structural_bounds r
  have hwidth:=hs.width
  have hten:=hs.ten
  have h0:=StageResize.bitLength_le r.stackWidth
  have h1:=StageResize.bitLength_le (r.stackWidth+1)
  have hw : (natWord r.stackWidth).length ≤ 3*r.setupStructuralMagnitude := by
    rw [NearCubicGates.Close.Cells.natWord_length]
    omega
  have hw1 : (natWord (r.stackWidth+1)).length ≤ 3*r.setupStructuralMagnitude := by
    rw [NearCubicGates.Close.Cells.natWord_length]
    omega
  refine ⟨hw,hw1,?_,?_⟩
  · rw [List.length_append,fixed_integer_bytes.1]
    omega
  · rw [List.length_append,fixed_integer_bytes.2]
    omega

theorem structural_powers (r : TermCutRequest) :
    r.setupStructuralMagnitude ≤ r.setupStructuralMagnitude^9 ∧
    r.setupStructuralMagnitude^3 ≤ r.setupStructuralMagnitude^9 ∧
    r.setupStructuralMagnitude^6 ≤ r.setupStructuralMagnitude^9 := by
  have hs:=(structural_bounds r).ten
  exact ⟨Nat.le_self_pow (by decide) _,Nat.pow_le_pow_right (by omega) (by decide),
    Nat.pow_le_pow_right (by omega) (by decide)⟩

end NearQuarticWires.StageTupleSetupCost
