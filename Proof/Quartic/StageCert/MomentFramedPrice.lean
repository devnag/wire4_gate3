import Proof.Quartic.StageCert.MomentFramedMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicGates.Close.Cells
open StageFormulaMetadata

/-- `prop:time`, paper/paper.tex: adding the
literal outer frame to the actual formatter preserves its fourth
power source-word clock, including all marked output operations. -/
theorem MomentRequest.framedFormatterBudget_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.framedFormatterBudget≤10000000000000000*(r.packet.word.length+1)^4 := by
  have hs := formatterSteps_le r.validPacket.val
    (NearCubicGates.Close.Interfaces.Formats.toks r.validPacket.formula)
    r.validPacket.source r.validPacket.mode
  change r.validPacket.steps≤1000000*(r.packet.word.length+1)^2 at hs
  have hmono := finiteBudget_mono StageRecovery.packetCallee VV MM r.packet.word
    (3*r.validPacket.steps+2) (3000000*(r.packet.word.length+1)^2+2) (by omega)
  have hTS : TSK StageRecovery.packetCallee=3 := rfl
  unfold MomentRequest.framedFormatterBudget
  refine hmono.trans ?_
  dsimp only [finiteBudget,finiteInitializeCost,finiteSetupACost,finiteWidth,costB,costC]
  rw [hTS]
  norm_num [VV,MM]
  ring_nf
  omega

/-- `prop:time`, paper/paper.tex: the exact
framed source's fixed coefficient includes its actual binary
formatter and both stream handoffs. -/
def framedScaleCoefficient : ℕ :=
  4*100000000000000+4*(10000000000000000*1000000^4)+12

noncomputable def framedPriceCoefficient (B1 B2 : ℕ) : ℕ :=
  framedScaleCoefficient*(momentRuntimeCoefficient B1 B2)^16

noncomputable def framedPriceExponent (B1 B2 : ℕ) : ℕ :=
  16*momentRuntimeExponent B1 B2

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete actual framed source keeps its full
fourth tuple power explicit, on all proposed witnesses. -/
theorem MomentRequest.framedSourceBudget_scale {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.framedSourceBudget≤framedScaleCoefficient*r.runtimeScale^16*
      (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := by
  let S := r.runtimeScale
  let P := ((Builder.allGates r.call).length+1)^r.selected.1.Xmax
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hP : 1≤P := Nat.pow_pos (Nat.succ_pos _)
  have hM : (Builder.allGates r.call).length^r.selected.1.Xmax≤P^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right hP (by decide : 1≤4))
  have hsrc : r.sourceBudget≤100000000000000*S^16*P^4 := by
    calc
      _≤100000000000000*(Builder.allGates r.call).length^r.selected.1.Xmax*S^5 := r.sourceBudget_le
      _≤100000000000000*P^4*S^16 := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (Nat.pow_le_pow_right hS (by decide))
      _=_ := by ring
  have hfmt : r.framedFormatterBudget≤(10000000000000000*1000000^4)*S^16*P^4 := by
    calc
      _≤10000000000000000*(r.packet.word.length+1)^4 := r.framedFormatterBudget_le
      _≤10000000000000000*(1000000*S^4*P)^4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left r.packet_length_scale 4)
      _=_ := by ring
  have hp : 1≤S^16*P^4 := Nat.mul_pos (Nat.pow_pos hS) (Nat.pow_pos hP)
  change 4*r.sourceBudget+4*r.framedFormatterBudget+12≤framedScaleCoefficient*S^16*P^4
  unfold framedScaleCoefficient
  nlinarith only [hsrc,hfmt,hp]

private theorem framed_price_rearrange (P C b E : ℕ) :
    framedScaleCoefficient*(C*b^E)^16*P^4=
      (framedScaleCoefficient*C^16)*b^(16*E)*P^4 := by
  rw [mul_pow,←pow_mul,Nat.mul_comm E 16]
  ring

/-- `prop:time`, paper/paper.tex: all physical
framed-source parameters have fixed original-arity polynomial bounds. -/
theorem MomentRequest.framedSourceBudget_arity {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.framedSourceBudget≤framedPriceCoefficient B1 B2*
      (r.call.n+1)^framedPriceExponent B1 B2*
      (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := by
  calc
    _≤framedScaleCoefficient*r.runtimeScale^16*
        (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 := r.framedSourceBudget_scale
    _≤framedScaleCoefficient*(momentRuntimeCoefficient B1 B2*
        (r.call.n+1)^momentRuntimeExponent B1 B2)^16*
        (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left r.runtimeScale_arity 16))
    _=_ := framed_price_rearrange _ _ _ _

/-- `prop:time`, paper/paper.tex: the entire
actual framed source over all N⁸ terms fits a fixed polynomial
per original column, under the unchanged selected degree guard. -/
theorem MomentRequest.framedSourceBudget_all_walks {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    2^(4*r.selected.1.k)*r.framedSourceBudget≤
      framedPriceCoefficient B1 B2*(r.call.n+1)^framedPriceExponent B1 B2*
        2^(r.call.n-r.selected.1.k) := by
  calc
    _≤2^(4*r.selected.1.k)*(framedPriceCoefficient B1 B2*
        (r.call.n+1)^framedPriceExponent B1 B2*
        (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4) :=
      Nat.mul_le_mul_left _ r.framedSourceBudget_arity
    _=(framedPriceCoefficient B1 B2*(r.call.n+1)^framedPriceExponent B1 B2)*
        (2^(4*r.selected.1.k)*(((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4) := by ring
    _≤_ := Nat.mul_le_mul_left _ r.formatted_tuple_reserve

end NearQuarticWires.StageCert.Tokens
