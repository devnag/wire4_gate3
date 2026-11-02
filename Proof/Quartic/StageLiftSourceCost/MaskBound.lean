import Proof.Quartic.StageLiftSourceCost.Scale
import Proof.Quartic.StageLiftSourceCost.Words

/-!
# Full guarded-tuple construction cost

`lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: each actual source mask
retains its G^X tuple count. All scalar and signed-word overhead is
polynomial in the original-header scale.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open NearCubicGates.Close.Cells StageLift StageCert.Tokens

private theorem mask_source_bound (G k X A B w S : ℕ) (hS : 1 ≤ S) (hG : 1 ≤ G)
    (hGS : G ≤ S) (hk : k ≤ S) (hX : X+1 ≤ S) (hA : A ≤ S) (hB : B ≤ S) (hw : w ≤ S) :
    maskSourceCost G k X A B w ≤ 10000*G^X*S^3 := by
  let M := G^X
  have hM : 1 ≤ M := Nat.pow_pos hG
  have hX' : X ≤ S := by omega
  have hS1 : S ≤ S^3 := Nat.le_self_pow (by decide) _
  have hS2 : S^2 ≤ S^3 := Nat.pow_le_pow_right hS (by decide)
  have hS0 : 1 ≤ S^3 := Nat.pow_pos hS
  have hMS1 := Nat.mul_le_mul_left M hS1
  have hMS2 := Nat.mul_le_mul_left M hS2
  have hMS0 := Nat.mul_le_mul_left M hS0
  have hS3M : S^3 ≤ M*S^3 := Nat.le_mul_of_pos_left _ hM
  calc
    maskSourceCost G k X A B w ≤
        S*((M*(S*((S+5*(S+S)+160*S+530)+4)+50*S+200+20)+30*S+40*S+400)+20)+200 := by
      unfold maskSourceCost
      dsimp only [M]
      gcongr
    _ ≤ 10000*M*S^3 := by
      nlinarith only [hMS1,hMS2,hS3M,hS1,hS2,hS0,hM]

theorem mask_source_scale {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    StageLiftMasks.originalMaskCost r ≤
      640000*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*(sourceScale r)^3 := by
  have hb:=sourceEnvelope_bounds r
  have hs:=(sourceScale_small r).2.1
  have hx:=StageLiftMasks.source_Xmax_le r
  have hw:=(source_word_lengths r).2.2.2.2
  have hh:=mask_source_bound (Builder.allGates r.child.call).length r.child.selected.1.k
    r.child.selected.1.Xmax (2*(sourceEnvelope r+1)) (4*(sourceEnvelope r+1))
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length
    (4*sourceScale r) (by omega) (print_originalPool_pos r)
    (by have hg:=hb.occurrences;omega) (by have hk:=hb.partition;omega)
    (by omega) (by omega) (by omega) (by omega)
  change StageLiftMasks.originalMaskCost r ≤
    10000*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*(4*sourceScale r)^3 at hh
  exact hh.trans_eq (by ring)

theorem full_masks_scale {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    let C:=printSourceContext B1 B2 (Greedy.printInput r)
    printMasksCost r C.Lk C.Bk ≤
      10000000*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*(sourceScale r)^4 := by
  let S:=sourceScale r
  let M:=(Builder.allGates r.child.call).length^r.child.selected.1.Xmax
  have hS : 1 ≤ S := by have hh:=(sourceScale_small r).1;omega
  have hM : 1 ≤ M := original_tuple_pos r
  have hP:=(source_word_lengths r).1
  have hE:=(sourceScale_small r).2.1
  have hL : (printSourceContext B1 B2 (Greedy.printInput r)).Lk ≤ S := by
    change (printSourceSizes B1 B2).Lk (leadOnes (Greedy.printInput r)) ≤ S
    rw [source_header]
    dsimp [S,sourceScale]
    omega
  have hB : (printSourceContext B1 B2 (Greedy.printInput r)).Bk ≤ S := by
    change (printSourceSizes B1 B2).Bk (leadOnes (Greedy.printInput r)) ≤ S
    rw [source_header]
    dsimp [S,sourceScale]
    omega
  have hm:=mask_source_scale r
  have h3 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h1 : S ≤ S^4 := Nat.le_self_pow (by decide) _
  have h0 : 1 ≤ S^4 := Nat.pow_pos hS
  have hM3:=Nat.mul_le_mul_left M h3
  have hM4:=Nat.mul_le_mul_right (S^4) hM
  have hE4:=Nat.pow_le_pow_left hE 4
  dsimp only [printMasksCost,completeMaskSourceCost]
  change 8*(StageLiftMasks.originalMaskCost r+20)+20+8*(_+_+9*(preparedWordOf r).length+
    80*(sourceEnvelope r+1)+500)+10000*(sourceEnvelope r+1)^4 ≤ 10000000*M*S^4
  change StageLiftMasks.originalMaskCost r ≤ 640000*M*S^3 at hm
  change (preparedWordOf r).length ≤ S at hP
  change sourceEnvelope r+1 ≤ S at hE
  change (sourceEnvelope r+1)^4 ≤ S^4 at hE4
  nlinarith only [hm,hP,hE,hL,hB,hM3,hM4,h1,h0,hE4]

end NearQuarticWires.StageLiftSourceCost
