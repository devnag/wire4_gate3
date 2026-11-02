import Proof.Quartic.StageLiftSourceCost.Words

/-!
# Once-only acquisition of the original printer source

`lem:print`, Step 3 and `prop:time`, paper/paper.tex: the actual preparation parser,
Gamma retention and raw-index normalization are charged once. Raw
index length is never multiplied by the closed-walk census.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces StageLift

variable {B1 B2 : ℕ}

theorem parameter_read_scale (r : Greedy.PrintRequest B1 B2) :
    parameterReadCost r.child.selected.1 (preparedWordOf r).length ≤ 20000*(sourceScale r)^2 := by
  have hh:=StageCertTests.parameterReadCost_le_word r.child.selected.1 (preparedWordOf r).length
  have hp:=source_word_lengths r
  have hs : 1 ≤ sourceScale r := by have h:=(sourceScale_small r).1;omega
  calc
    _ ≤ 5000*((Program.parametersWord r.child.selected.1).length+1)*((preparedWordOf r).length+1) := hh
    _ ≤ 5000*(sourceScale r+1)*(sourceScale r+1) := by gcongr;exact hp.2.2.1;exact hp.1
    _ ≤ _ := by nlinarith

theorem compact_acquire_scale (r : Greedy.PrintRequest B1 B2) :
    StageMain.Compact.acquireCost r.child.call r.child.selected.1
      (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness) ≤ 100000*(sourceScale r)^3 := by
  have hp:=source_word_lengths r
  have hs : 1 ≤ sourceScale r := by have h:=(sourceScale_small r).1;omega
  have hS1 : sourceScale r ≤ (sourceScale r)^3 := Nat.le_self_pow (by decide) _
  have hS2 : (sourceScale r)^2 ≤ (sourceScale r)^3 := Nat.pow_le_pow_right hs (by decide)
  have hS0 : 1 ≤ (sourceScale r)^3 := Nat.pow_pos hs
  calc
    _ ≤ 3000*(sourceScale r+1)^3+4000*(sourceScale r+1)^2+12*sourceScale r+11*sourceScale r+40 := by
      have hcall:=Nat.pow_le_pow_left (Nat.add_le_add_right hp.2.1 1) 3
      have hparams:=Nat.pow_le_pow_left (Nat.add_le_add_right hp.2.2.1 1) 2
      unfold StageMain.Compact.acquireCost
      omega
    _ ≤ _ := by nlinarith only [hS1,hS2,hS0]

theorem index_target_scale (r : Greedy.PrintRequest B1 B2) :
    indexTargetsCost r (Greedy.printIndexWord r).length 0 ≤
      2000*sourceScale r*((Greedy.printIndexWord r).length+1) := by
  have hJ:=(sourceEnvelope_bounds r).chains
  have hE:=(sourceScale_small r).2.1
  have hd:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self (printDigitList r).length
  have hr:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self (printResidueList r).length
  rw [print_digit_count] at hd
  rw [printResidueList_length] at hr
  have hm:=Nat.mul_le_mul_right (32*(Greedy.printIndexWord r).length+128)
    (show 2*r.child.selected.1.J+2 ≤ 2*sourceScale r by omega)
  unfold indexTargetsCost
  rw [print_digit_count,printResidueList_length]
  nlinarith only [hm,hd,hr,hJ,hE]

theorem print_source_scale (r : Greedy.PrintRequest B1 B2) :
    printSourceCost r (preparedWordOf r).length ≤ 100000*(sourceScale r)^3+
      8*(listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length := by
  have hp:=source_word_lengths r
  have hpar:=parameter_read_scale r
  have hs : 1 ≤ sourceScale r := by have h:=(sourceScale_small r).1;omega
  have hS1 : sourceScale r ≤ (sourceScale r)^3 := Nat.le_self_pow (by decide) _
  have hS2 : (sourceScale r)^2 ≤ (sourceScale r)^3 := Nat.pow_le_pow_right hs (by decide)
  have hS0 : 1 ≤ (sourceScale r)^3 := Nat.pow_pos hs
  calc
    _ ≤ 3000*(sourceScale r+1)^3+12*sourceScale r+20000*(sourceScale r)^2+
      8*sourceScale r+8*(listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length+27 := by
      have hcall:=Nat.pow_le_pow_left (Nat.add_le_add_right hp.2.1 1) 3
      unfold printSourceCost
      omega
    _ ≤ _ := by nlinarith only [hS1,hS2,hS0]

theorem carrier_startup_scale (r : Greedy.PrintRequest B1 B2) :
    carrierStartupCost r ≤ 1000000*(r.child.cellCall.seed.N^8*(sourceScale r)^3+
      (sourceScale r)^3*((Greedy.printIndexWord r).length+1)) := by
  let S:=sourceScale r
  let N:=r.child.cellCall.seed.N^8
  let I:=(Greedy.printIndexWord r).length
  have hsmall:=sourceScale_small r
  have hs : 1 ≤ S := by dsimp [S];omega
  have hn : 1 ≤ N := walkCount_pos r
  have hP:=(source_word_lengths r).1
  have hc:=(source_word_lengths r).2.1
  have hA:=compact_acquire_scale r
  have hR:=print_source_scale r
  have hI:=index_target_scale r
  have hg:=gamma_word_length r
  have hb:=sourceEnvelope_bounds r
  have hnb:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self r.prime
  have hnn:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self r.child.call.n
  have hnp:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self (preparedWordOf r).length
  have hwalk:=source_walk_counter_bits r
  have hkind : natBitLength (kindTag r.child.call.kind) ≤ 3 := by cases r.child.call.kind <;> decide
  have hS1 : S ≤ S^3 := Nat.le_self_pow (by decide) _
  have hS2 : S^2 ≤ S^3 := Nat.pow_le_pow_right hs (by decide)
  have hS0 : 1 ≤ S^3 := Nat.pow_pos hs
  have hNS:=Nat.mul_le_mul_right (S^3) hn
  have hN2:=Nat.mul_le_mul_left N hS2
  have hIS:=Nat.mul_le_mul_right (I+1) hS1
  have hIS0:=Nat.mul_le_mul_left (S^3) (show 1 ≤ I+1 by omega)
  unfold carrierStartupCost sourceAcquisitionCost cachedRequestCost carrierMetadataCost
  rw [print_digit_count,printResidueList_length]
  change _ ≤ 1000000*(N*S^3+S^3*(I+1))
  change StageMain.Compact.acquireCost _ _ _ ≤ 100000*S^3 at hA
  change printSourceCost _ _ ≤ 100000*S^3+8*_ at hR
  change indexTargetsCost _ _ _ ≤ 2000*S*(I+1) at hI
  change _ ≤ 30*N*S^2 at hg
  change (preparedWordOf r).length ≤ S at hP
  change (callWord r.child.call).length ≤ S at hc
  have he : sourceEnvelope r+1 ≤ S := hsmall.2.1
  have hsn : r.child.call.n+1 ≤ S := hsmall.2.2
  nlinarith only [hA,hR,hI,hg,hP,hc,hb.exponent,hb.chains,hb.prime,he,hsn,
    hnb,hnn,hnp,hwalk,hkind,hS1,hS0,hNS,hN2,hIS,hIS0]

end NearQuarticWires.StageLiftSourceCost
