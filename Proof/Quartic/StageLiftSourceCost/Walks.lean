import Proof.Quartic.StageLiftSourceCost.MaskBound

/-!
# Actual per-walk and all-walk source clocks

`lem:print` and `prop:time`, paper/paper.tex: the complete framed payload includes original Gamma,
eight masks and amplified residue syntax. Its all-walk loop keeps
one explicit G^X enumeration factor and fixed polynomial overhead.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open NearCubicGates.Close.Cells StageLift

variable {B1 B2 : ℕ}

theorem walk_payload_scale (r : Greedy.PrintRequest B1 B2) :
    let C:=printSourceContext B1 B2 (Greedy.printInput r)
    walkPayloadCost r C.Lk C.Bk ≤
      2000000000000*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*(sourceScale r)^30 := by
  let S:=sourceScale r
  let M:=(Builder.allGates r.child.call).length^r.child.selected.1.Xmax
  have hs : 1 ≤ S := by have hh:=(sourceScale_small r).1;omega
  have hm : 1 ≤ M := original_tuple_pos r
  have hmask:=full_masks_scale r
  have hE : sourceEnvelope r+1 ≤ S := (sourceScale_small r).2.1
  have hE2:=Nat.pow_le_pow_left hE 2
  have hE30:=Nat.pow_le_pow_left hE 30
  have h1 : S ≤ S^30 := Nat.le_self_pow (by decide) _
  have h2 : S^2 ≤ S^30 := Nat.pow_le_pow_right hs (by decide)
  have h4 : S^4 ≤ S^30 := Nat.pow_le_pow_right hs (by decide)
  have h0 : 1 ≤ S^30 := Nat.pow_pos hs
  have hM4:=Nat.mul_le_mul_left M h4
  have hM30:=Nat.mul_le_mul_right (S^30) hm
  dsimp only at hmask ⊢
  unfold walkPayloadCost walkHeadCost
  change _ ≤ 2000000000000*M*S^30
  change _ ≤ 10000000*M*S^4 at hmask
  nlinarith only [hmask,hE,hE2,hE30,h1,h2,h0,hM4,hM30]

theorem all_walk_scale (r : Greedy.PrintRequest B1 B2) :
    let C:=printSourceContext B1 B2 (Greedy.printInput r)
    allWalkSourceCost r C.Lk C.Bk ≤
      10000000000000*r.child.cellCall.seed.N^8*
        (Builder.allGates r.child.call).length^r.child.selected.1.Xmax*(sourceScale r)^30 := by
  let S:=sourceScale r
  let M:=(Builder.allGates r.child.call).length^r.child.selected.1.Xmax
  let N:=r.child.cellCall.seed.N^8
  have hs : 1 ≤ S := by have hh:=(sourceScale_small r).1;omega
  have hm : 1 ≤ M := original_tuple_pos r
  have hn : 1 ≤ N := walkCount_pos r
  have hp:=walk_payload_scale r
  have hE2:=Nat.pow_le_pow_left (sourceScale_small r).2.1 2
  have h2 : S^2 ≤ S^30 := Nat.pow_le_pow_right hs (by decide)
  have h0 : 1 ≤ S^30 := Nat.pow_pos hs
  have hM30:=Nat.mul_le_mul_right (S^30) hm
  have hpacket : walkPacketCost r
      (printSourceContext B1 B2 (Greedy.printInput r)).Lk
      (printSourceContext B1 B2 (Greedy.printInput r)).Bk+4 ≤ 7000000000000*M*S^30 := by
    unfold walkPacketCost
    change _ ≤ 2000000000000*M*S^30 at hp
    change (sourceEnvelope r+1)^2 ≤ S^2 at hE2
    nlinarith only [hp,hE2,h2,h0,hM30]
  have hh:=Nat.mul_le_mul_left N hpacket
  have hNM : 1 ≤ N*M*S^30 := Nat.mul_pos (Nat.mul_pos hn hm) h0
  dsimp only [allWalkSourceCost]
  change N*(_+4)+4 ≤ 10000000000000*N*M*S^30
  nlinarith only [hh,hNM]

end NearQuarticWires.StageLiftSourceCost
