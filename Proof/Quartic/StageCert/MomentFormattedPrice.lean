import Proof.Quartic.StageCert.MomentFormattedMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires

/-- `prop:time`, paper/paper.tex: the exact
source and formatter contribute fixed coefficients to one complete
ordinary runtime bound, including both physical handoffs. -/
def formattedScaleCoefficient : ℕ :=
  4*100000000000000+4*(1000000000000000*1000000^4)+12

noncomputable def formattedPriceCoefficient (B1 B2 : ℕ) : ℕ :=
  formattedScaleCoefficient*(momentRuntimeCoefficient B1 B2)^16

noncomputable def formattedPriceExponent (B1 B2 : ℕ) : ℕ :=
  16*momentRuntimeExponent B1 B2

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold source followed by exact formatting
keeps its complete fourth-power tuple factor explicit. -/
theorem MomentRequest.formattedBudget_scale {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.formattedBudget≤formattedScaleCoefficient*r.runtimeScale^16*
      (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := by
  let S := r.runtimeScale
  let P := ((Builder.allGates r.call).length+1)^r.selected.1.Xmax
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hP : 1≤P := Nat.pow_pos (Nat.succ_pos _)
  have hM : (Builder.allGates r.call).length^r.selected.1.Xmax≤P^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right hP (by decide : 1≤4))
  have hS5 : S^5≤S^16 := Nat.pow_le_pow_right hS (by decide)
  have hsrc : r.sourceBudget≤100000000000000*S^16*P^4 := by
    calc
      _≤100000000000000*(Builder.allGates r.call).length^r.selected.1.Xmax*S^5 := r.sourceBudget_le
      _≤100000000000000*P^4*S^16 := by gcongr
      _=_ := by ring
  have hfmt := r.formatterBudget_scale
  change r.validPacket.budget≤(1000000000000000*1000000^4)*S^16*P^4 at hfmt
  have hp : 1≤S^16*P^4 := Nat.mul_pos (Nat.pow_pos hS) (Nat.pow_pos hP)
  change 4*r.sourceBudget+4*r.validPacket.budget+12≤formattedScaleCoefficient*S^16*P^4
  unfold formattedScaleCoefficient
  nlinarith only [hsrc,hfmt,hp]

private theorem formatted_price_rearrange (P C b E : ℕ) :
    formattedScaleCoefficient*(C*b^E)^16*P^4=
      (formattedScaleCoefficient*C^16)*b^(16*E)*P^4 := by
  rw [mul_pow,←pow_mul,Nat.mul_comm E 16]
  ring

/-- `prop:time`, paper/paper.tex: fixed arity
powers pay all ordinary source and formatter dimensions uniformly
over the literal proposed witness and every test index. -/
theorem MomentRequest.formattedBudget_arity {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.formattedBudget≤formattedPriceCoefficient B1 B2*
      (r.call.n+1)^formattedPriceExponent B1 B2*
      (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := by
  calc
    _≤formattedScaleCoefficient*r.runtimeScale^16*
        (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := r.formattedBudget_scale
    _≤formattedScaleCoefficient*(momentRuntimeCoefficient B1 B2*
        (r.call.n+1)^momentRuntimeExponent B1 B2)^16*
        (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left r.runtimeScale_arity 16))
    _=_ := formatted_price_rearrange _ _ _ _

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual formatter's fourth tuple power over
all exact closed walks fits the unchanged degree comparison. -/
theorem MomentRequest.formatted_tuple_reserve {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    2^(4*r.selected.1.k)*(((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4≤
      2^(r.call.n-r.selected.1.k) := by
  let G := (Builder.allGates r.call).length
  let D := 16*r.selected.1.Xmax+8*r.selected.1.k
  have hV : G+1≤r.selected.1.Uocc := by
    have hh := r.source_occurrence_guard
    dsimp only [G]
    omega
  have hp : ((G+1)^r.selected.1.Xmax)^4≤(G+1)^(3*D) := by
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (Nat.succ_pos G) (by dsimp only [D]; omega)
  exact (Nat.mul_le_mul_left _ hp).trans
    (r.rules.recovery_all_walks_reserve G D hV r.source_degree_guard)

/-- `prop:time`, paper/paper.tex: the complete
actual source-to-signed-Formula word function, over all N⁸
terms, is charged to one fixed arity polynomial per original column. -/
theorem MomentRequest.formattedBudget_all_walks {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    2^(4*r.selected.1.k)*r.formattedBudget≤
      formattedPriceCoefficient B1 B2*(r.call.n+1)^formattedPriceExponent B1 B2*
        2^(r.call.n-r.selected.1.k) := by
  calc
    _≤2^(4*r.selected.1.k)*(formattedPriceCoefficient B1 B2*
        (r.call.n+1)^formattedPriceExponent B1 B2*
        (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4) :=
      Nat.mul_le_mul_left _ r.formattedBudget_arity
    _=(formattedPriceCoefficient B1 B2*(r.call.n+1)^formattedPriceExponent B1 B2)*
        (2^(4*r.selected.1.k)*(((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4) := by ring
    _≤_ := Nat.mul_le_mul_left _ r.formatted_tuple_reserve

end NearQuarticWires.StageCert.Tokens
