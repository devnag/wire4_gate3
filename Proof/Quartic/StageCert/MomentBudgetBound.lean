import Proof.Quartic.StageCert.MomentStepBounds

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires
open NearCubicGates.Close.Cells

/-- `lem:print` and `prop:time`, paper/paper.tex: exact header emission and physical payload framing
preserve the actual G^X construction factor in the source clock. -/
theorem MomentRequest.packetSteps_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.packetSteps≤20000000*(Builder.allGates r.call).length^r.selected.1.Xmax*r.runtimeScale^3 := by
  let S := r.runtimeScale
  let M := (Builder.allGates r.call).length^r.selected.1.Xmax
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hM : 1≤M := Nat.pow_pos r.pool_pos
  have hp := r.payloadSteps_le
  change r.payloadSteps≤4000000*M*S^3 at hp
  have hscale : r.bodyScale≤S := r.runtimeScale_basic.2.1
  have hS1 : S≤S^3 := Nat.le_self_pow (by decide) _
  have hS0 : 1≤S^3 := Nat.pow_pos hS
  have hMS : S^3≤M*S^3 := Nat.le_mul_of_pos_left _ hM
  change 4*(40*(32*r.bodyScale+10)+43)+3*r.payloadSteps+700≤20000000*M*S^3
  nlinarith only [hp,hscale,hS1,hS0,hMS]

/-- `prop:time`, paper/paper.tex: the actual
ordinary structural frontend has its complete binary compilation,
finite-call and source-restoration cost included in the fifth scale power. -/
theorem MomentRequest.frontendBudget_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.frontendBudget≤5000000000*r.runtimeScale^5 := by
  let S := r.runtimeScale
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hword : r.word.length≤S := r.runtimeScale_basic.2.2
  have hf := r.frontendSteps_le
  change r.frontendSteps≤120000*S^3 at hf
  have hS1 : S≤S^3 := Nat.le_self_pow (by decide) _
  have hS0 : 1≤S^3 := Nat.pow_pos hS
  have hsum : 3*r.frontendSteps+8+r.word.length+1≤500000*S^3 := by omega
  have hc : r.frontendBudget≤10000*S^2*(3*r.frontendSteps+8+r.word.length+1) := by
    simpa only [List.append_nil,MomentRequest.frontendBudget] using
      r.compiler_budget_le [] (3*r.frontendSteps+8)
  calc
    r.frontendBudget≤10000*S^2*(3*r.frontendSteps+8+r.word.length+1) := hc
    _≤10000*S^2*(500000*S^3) := Nat.mul_le_mul_left _ hsum
    _=5000000000*S^5 := by ring

/-- `prop:time`, paper/paper.tex: the actual
computed-flag input has only eight more bits than the original source;
its complete length is included in the runtime scale. -/
theorem MomentRequest.flagged_length_runtime {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.flaggedWord.length≤r.runtimeScale := by
  have he : (momentFlagEdges r.test).length≤8 := by
    cases r.test <;> simp only [momentFlagEdges,List.length_cons,List.length_nil,List.length_ofFn] <;> omega
  have hword : r.word.length≤r.bodyScale := by unfold MomentRequest.bodyScale; omega
  simp only [MomentRequest.flaggedWord,List.length_append,structuralFlagList,List.length_map]
  dsimp only [MomentRequest.runtimeScale]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the signed packet body's ordinary machine clock
includes the full G^X tuple syntax construction and every compiler,
source, head-restoration and framed-output operation. -/
theorem MomentRequest.bodyBudget_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.bodyBudget≤2000000000000*(Builder.allGates r.call).length^r.selected.1.Xmax*r.runtimeScale^5 := by
  let S := r.runtimeScale
  let M := (Builder.allGates r.call).length^r.selected.1.Xmax
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hM : 1≤M := Nat.pow_pos r.pool_pos
  have hr := r.readSteps_le
  change r.readSteps≤110000*S^3 at hr
  have hp := r.packetSteps_le
  change r.packetSteps≤20000000*M*S^3 at hp
  have hi : r.flaggedWord.length≤S := r.flagged_length_runtime
  have hS1 : S≤S^3 := Nat.le_self_pow (by decide) _
  have hS0 : 1≤S^3 := Nat.pow_pos hS
  have hMS : S^3≤M*S^3 := Nat.le_mul_of_pos_left _ hM
  have hsum : 3*(r.readSteps+r.packetSteps+1)+8+r.flaggedWord.length+1≤200000000*M*S^3 := by
    nlinarith only [hr,hp,hi,hS1,hS0,hMS]
  have hc : r.bodyBudget≤10000*S^2*(3*(r.readSteps+r.packetSteps+1)+8+r.flaggedWord.length+1) := by
    simpa only [MomentRequest.flaggedWord,MomentRequest.bodyBudget] using
      r.compiler_budget_le (structuralFlagList r (momentFlagEdges r.test))
        (3*(r.readSteps+r.packetSteps+1)+8)
  calc
    r.bodyBudget≤10000*S^2*(3*(r.readSteps+r.packetSteps+1)+8+r.flaggedWord.length+1) := hc
    _≤10000*S^2*(200000000*M*S^3) := Nat.mul_le_mul_left _ hsum
    _=2000000000000*M*S^5 := by ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the entire actual cold source machine has an explicit
runtime bound retaining its full tuple enumeration factor. This is the
physical source clock, not an assumed cost for an expression supplier. -/
theorem MomentRequest.sourceBudget_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.sourceBudget≤100000000000000*(Builder.allGates r.call).length^r.selected.1.Xmax*r.runtimeScale^5 := by
  let S := r.runtimeScale
  let M := (Builder.allGates r.call).length^r.selected.1.Xmax
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hM : 1≤M := Nat.pow_pos r.pool_pos
  have hf := r.frontendBudget_le
  change r.frontendBudget≤5000000000*S^5 at hf
  have hb := r.bodyBudget_le
  change r.bodyBudget≤2000000000000*M*S^5 at hb
  have hS0 : 1≤S^5 := Nat.pow_pos hS
  have hMS : S^5≤M*S^5 := Nat.le_mul_of_pos_left _ hM
  change 4*r.frontendBudget+4*r.bodyBudget+12≤100000000000000*M*S^5
  nlinarith only [hf,hb,hS0,hMS]

end NearQuarticWires.StageCert.Tokens
