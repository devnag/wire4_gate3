import Proof.Quartic.StageCarrierEnvelope.SourceCost
import Proof.Quartic.StageMain.CompilerRuntime

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.CounterMachine.PrefixProg

/-- `prop:time`, paper/paper.tex: all actual
compiler dimensions depend only on the physically read finite prefix. -/
def profileScale (P : ℕ) : ℕ := metadataSizes.W (natBitLength P)+1000+2+VV+MM+P+1000

def profileCoefficient : ℕ := 6003+VV+MM

/-- `prop:time`, paper/paper.tex: the exact
prefix-derived binary allocator has quadratic finite-prefix width. -/
theorem metadata_width_upper (P : ℕ) : metadataSizes.W (natBitLength P)≤4000*(P+1)^2 := by
  have hh:=Nat.pow_le_pow_left (pow_nbl_le P) 2
  change 2^(2*natBitLength P)*1000≤_
  rw [←pow_mul,Nat.mul_comm (natBitLength P)] at hh
  nlinarith only [hh]

/-- `prop:time`, paper/paper.tex: the actual
fixed compiler scale is independent of the following Terms carrier. -/
theorem profileScale_bound (P : ℕ) : profileScale P≤ profileCoefficient*(P+1)^2 := by
  have hw:=metadata_width_upper P
  have hp : P+1≤(P+1)^2 := Nat.le_self_pow (by decide) _
  have h1 : 1≤(P+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hc : 2002+VV+MM≤(2002+VV+MM)*(P+1)^2 := Nat.le_mul_of_pos_right _ (by omega)
  unfold profileScale profileCoefficient
  nlinarith only [hw,hp,hc]

/-- `prop:time`, paper/paper.tex: this uses
Cells' real setup, compilation and teardown costs; the entire actual
carrier length and the source clock occur only linearly. -/
theorem metadata_compiler_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    metadataBudget r≤10000*(profileScale (StageLift.preparedWordOf r).length)^2*
      (metadataSteps r+(StagePrint.TermsCarrier.word r).length+1) := by
  unfold metadataBudget
  apply StageMain.Runtime.langBudget_le
  · unfold profileScale;omega
  · unfold profileScale;omega
  · unfold profileScale;omega
  · change 3≤ profileScale (StageLift.preparedWordOf r).length
    unfold profileScale;omega
  · change 1000≤ profileScale (StageLift.preparedWordOf r).length
    unfold profileScale;omega
  · change 2≤ profileScale (StageLift.preparedWordOf r).length
    unfold profileScale;omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rw [carrier_header]
    have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_succ (StageLift.preparedWordOf r).length
    unfold profileScale;omega
  · rw [carrier_header]
    unfold profileScale;omega
  · simp only [metadataSizes,Sz.Lk,Nat.mul_zero]
    exact Nat.zero_le _
  · simp only [metadataSizes,Sz.Bk,Nat.mul_zero]
    exact Nat.zero_le _

/-- `prop:time`, paper/paper.tex: the actual
metadata program budget is linear in the genuine full carrier length,
with only a fixed polynomial of its finite original preparation. -/
theorem metadataBudget_prefix_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    metadataBudget r≤10000*profileCoefficient^2*(10^8+1)*
      ((StagePrint.TermsCarrier.word r).length+1)*((StageLift.preparedWordOf r).length+1)^7 := by
  let P:=(StageLift.preparedWordOf r).length
  let I:=(StagePrint.TermsCarrier.word r).length
  have hsteps:=metadataSteps_bound r
  change metadataSteps r≤10^8*(P+1)^3 at hsteps
  have h1 : 1≤(P+1)^3 := Nat.one_le_pow _ _ (by omega)
  have ha : 10^8*(P+1)^3≤10^8*(P+1)^3*(I+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hi : I+1≤(P+1)^3*(I+1) := by simpa only [one_mul] using Nat.mul_le_mul_right (I+1) h1
  have htotal : metadataSteps r+I+1≤(10^8+1)*(P+1)^3*(I+1) := by nlinarith only [hsteps,ha,hi]
  have hscale:=Nat.pow_le_pow_left (profileScale_bound P) 2
  calc
    _≤10000*(profileScale P)^2*(metadataSteps r+I+1) := metadata_compiler_bound r
    _≤10000*(profileCoefficient*(P+1)^2)^2*((10^8+1)*(P+1)^3*(I+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hscale) htotal
    _=_ := by dsimp only [P,I];rw [mul_pow];ring

/-- `prop:time`, paper/paper.tex: original
normalized call bounds convert that SAME physical metadata budget to
linear carrier length times a fixed original-arity polynomial. -/
theorem metadataBudget_linear (B1 B2 : ℕ) : ∃K e : ℕ,∀r : Greedy.PrintRequest B1 B2,
    metadataBudget r≤K*((StagePrint.TermsCarrier.word r).length+1)*(r.child.call.n+1)^e := by
  let K0:=10000*profileCoefficient^2*(10^8+1)
  refine ⟨K0*(StageMain.Compact.capacityCoefficient B1+1)^7,
    StageMain.Compact.capacityExponent B1 B2*7,fun r=>?_⟩
  have hp:=StageMain.Compact.compactInput_length_arity r.child.dispatched r.child.witness
  change (StageLift.preparedWordOf r).length≤StageMain.Compact.capacityCoefficient B1*
    (r.child.call.n+1)^StageMain.Compact.capacityExponent B1 B2 at hp
  have h1 : 1≤(r.child.call.n+1)^StageMain.Compact.capacityExponent B1 B2 := Nat.one_le_pow _ _ (by omega)
  have hsource : (StageLift.preparedWordOf r).length+1≤(StageMain.Compact.capacityCoefficient B1+1)*
      (r.child.call.n+1)^StageMain.Compact.capacityExponent B1 B2 := by nlinarith only [hp,h1]
  calc
    _≤K0*((StagePrint.TermsCarrier.word r).length+1)*((StageLift.preparedWordOf r).length+1)^7 :=
      metadataBudget_prefix_bound r
    _≤K0*((StagePrint.TermsCarrier.word r).length+1)*
        ((StageMain.Compact.capacityCoefficient B1+1)*(r.child.call.n+1)^StageMain.Compact.capacityExponent B1 B2)^7 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsource _)
    _=_ := by rw [mul_pow,←pow_mul];ring

end NearQuarticWires.StageCarrierEnvelope
