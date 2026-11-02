import Proof.Quartic.StageCert.MomentRuntimeScale

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires
open NearCubicGates.Close.Cells
open StageMain.Compact

private theorem mask_source_bound (G k X A B w S : ℕ) (hS : 1≤S) (hG : 1≤G)
    (hGS : G≤S) (hk : k≤S) (hX : X+1≤S) (hA : A≤S) (hB : B≤S) (hw : w≤S) :
    maskSourceCost G k X A B w≤10000*G^X*S^3 := by
  let M := G^X
  have hM : 1≤M := Nat.pow_pos hG
  have hX' : X≤S := by omega
  have hS1 : S≤S^3 := Nat.le_self_pow (by decide) _
  have hS2 : S^2≤S^3 := Nat.pow_le_pow_right hS (by decide)
  have hS0 : 1≤S^3 := Nat.pow_pos hS
  have hMS1 := Nat.mul_le_mul_left M hS1
  have hMS2 := Nat.mul_le_mul_left M hS2
  have hMS0 := Nat.mul_le_mul_left M hS0
  have hS3M : S^3≤M*S^3 := Nat.le_mul_of_pos_left _ hM
  calc
    maskSourceCost G k X A B w≤
        S*((M*(S*((S+5*(S+S)+160*S+530)+4)+50*S+200+20)+30*S+40*S+400)+20)+200 := by
      unfold maskSourceCost
      dsimp only [M]
      gcongr
    _≤10000*M*S^3 := by
      nlinarith only [hMS1,hMS2,hS3M,hS1,hS2,hS0,hM]

/-- `prop:time`, paper/paper.tex: the actual
retained witness and active rate-list lengths fit the source runtime
scale, uniformly over arbitrary proposed source bits. -/
theorem MomentRequest.runtime_source_lengths {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.retainedWitness.length≤r.runtimeScale ∧ r.selected.1.factors.length≤r.runtimeScale := by
  have hword := r.runtimeScale_basic.2.2
  have hp : (compactInput r.call r.selected.1 r.retainedWitness).length≤r.runtimeScale := by
    change (compactInput r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)).length≤r.runtimeScale
    rw [←StageMain.Compact.prepWord_eq_compact r.dispatched r.witness]
    exact r.prep_length_le.trans hword
  have hw := (StageMain.Runtime.compact_lengths r.call r.selected.1 r.retainedWitness).2.2.2
  have hJ : r.selected.1.J≤r.runtimeScale := by
    have hh := r.runtimeScale_basic.2.1
    dsimp only [MomentRequest.bodyScale] at hh
    omega
  exact ⟨hw.trans hp,(retainedFactors_length r.call r.rules).le.trans
    ((Nat.sub_le _ _).trans hJ)⟩

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: the source clock pays all G^X actual tuple addresses,
with only a fixed polynomial factor in the displayed runtime scale. -/
theorem MomentRequest.maskSteps_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    maskSourceCost (Builder.allGates r.call).length r.selected.1.k r.selected.1.Xmax
      r.atomBits (r.selected.1.Xmax+1) r.retainedWitness.length≤
        10000*(Builder.allGates r.call).length^r.selected.1.Xmax*r.runtimeScale^3 := by
  have hs := r.runtimeScale_basic
  have hk : r.selected.1.k≤r.runtimeScale := by dsimp only [MomentRequest.bodyScale] at hs; omega
  have hGS : (Builder.allGates r.call).length≤r.runtimeScale := by
    dsimp only [MomentRequest.bodyScale] at hs
    omega
  have hX : r.selected.1.Xmax+1≤r.runtimeScale := by dsimp only [MomentRequest.bodyScale] at hs; omega
  have hA : r.atomBits≤r.runtimeScale := by dsimp only [MomentRequest.bodyScale] at hs; omega
  exact mask_source_bound _ _ _ _ _ _ _ (by omega) r.pool_pos hGS hk hX hA hX r.runtime_source_lengths.1

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: all three exact payload branches
retain the actual G^X serialization factor in their source clocks. -/
theorem MomentRequest.payloadSteps_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.payloadSteps≤4000000*(Builder.allGates r.call).length^r.selected.1.Xmax*r.runtimeScale^3 := by
  let S := r.runtimeScale
  let M := (Builder.allGates r.call).length^r.selected.1.Xmax
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hM : 1≤M := Nat.pow_pos r.pool_pos
  have hs := r.runtimeScale_basic.2.1
  have hG : (Builder.allGates r.call).length≤S := by dsimp only [MomentRequest.bodyScale] at hs; omega
  have hk : r.selected.1.k≤S := by dsimp only [MomentRequest.bodyScale] at hs; omega
  have hA : r.atomBits≤S := by dsimp only [MomentRequest.bodyScale] at hs; omega
  have hC : r.coefficientBits≤S := by dsimp only [MomentRequest.bodyScale] at hs; omega
  have hw : r.retainedWitness.length≤S := r.runtime_source_lengths.1
  have hf : r.selected.1.factors.length≤S := r.runtime_source_lengths.2
  have hlog (v : ℕ) : natBitLength v≤v+1 := by
    unfold natBitLength
    have hh := Nat.log_le_self 2 v
    omega
  have hE8 : natBitLength (8*r.selected.1.k)≤8*S+1 :=
    (hlog _).trans (by omega)
  have hE2 : natBitLength (2*r.selected.1.k)≤2*S+1 :=
    (hlog _).trans (by omega)
  have hS1 : S≤S^3 := Nat.le_self_pow (by decide) _
  have hS2 : S^2≤S^3 := Nat.pow_le_pow_right hS (by decide)
  have hS0 : 1≤S^3 := Nat.pow_pos hS
  have hS3M : S^3≤M*S^3 := Nat.le_mul_of_pos_left _ hM
  have hm := r.maskSteps_le
  change maskSourceCost _ _ _ _ _ _≤10000*M*S^3 at hm
  have hcomplete : completeMaskSourceCost (Builder.allGates r.call).length r.selected.1.k
      r.selected.1.Xmax r.atomBits (r.selected.1.Xmax+1) r.retainedWitness.length≤80000*M*S^3+180 := by
    unfold completeMaskSourceCost
    nlinarith only [hm]
  have hp : r.populationSteps≤1000000*M*S^3 := by
    calc
      r.populationSteps≤S*(S+5*(S+S)+160*S+540)+40*(2*S+1)+540 := by
        unfold MomentRequest.populationSteps
        gcongr
      _≤1000000*M*S^3 := by nlinarith only [hS1,hS2,hS0,hS3M]
  have hd : r.digitSteps≤1000000*M*S^3 := by
    calc
      r.digitSteps≤80000*M*S^3+180+
          S*(12*S+6*S+8*(40*S+160*S+640)+160)+40*(8*S+1)+1510 := by
        unfold MomentRequest.digitSteps
        gcongr
      _≤1000000*M*S^3 := by nlinarith only [hS1,hS2,hS0,hS3M]
  have hfin : r.finalSteps≤1000000*M*S^3 := by
    calc
      r.finalSteps≤80000*M*S^3+180+
          S*(6*S+8*(40*S+160*S+640)+100)+40*(8*S+1)+1510 := by
        unfold MomentRequest.finalSteps
        gcongr
      _≤1000000*M*S^3 := by nlinarith only [hS1,hS2,hS0,hS3M]
  unfold MomentRequest.payloadSteps
  change _≤4000000*M*S^3
  nlinarith only [hp,hd,hfin,hS3M,hS0]

end NearQuarticWires.StageCert.Tokens
