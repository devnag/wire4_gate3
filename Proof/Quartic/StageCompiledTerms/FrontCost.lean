import Proof.Quartic.StageCompiledTerms.ListCosts

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- `prop:time`, paper/paper.tex: source
acquisition, prefix processing, packet iteration and final framing add
linearly under the same measured walk and per-packet bounds. -/
theorem front_ledger_bound (L B A P N U : ℕ)
    (hL : L≤3*N*U) (hB : B≤10*N*U) (hA : A≤N*U) (hP : P≤U)
    (hN : N≤N*U) (hU : U≤N*U) (hNU : 1≤N*U) :
    23*L+5+P+(400*(A+N)+1)+(200*B+50)+10≤10000*N*U := by
  nlinarith only [hL,hB,hA,hP,hN,hU,hNU]

/-- `prop:time`, paper/paper.tex: the generic
streaming carrier clock obeys its measured source, packet and output
bounds before the actual original-input source is substituted. -/
theorem RawCarrier.frontSteps_bound (r : RawCarrier) (N U : ℕ)
    (hcount : r.packets.length=N)
    (hin : r.word.length≤3*N*U) (hout : r.batchWord.length≤10*N*U)
    (hraw : (r.packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length≤N*U)
    (hprefix : prefixCost r.preparation N≤U)
    (hN : N≤N*U) (hU : U≤N*U) (hNU : 1≤N*U) :
    r.frontSteps≤10000*N*U := by
  unfold RawCarrier.frontSteps
  rw [hcount]
  exact front_ledger_bound _ _ _ _ N U hin hout hraw hprefix hN hU hNU

/-- `prop:time`, paper/paper.tex: the whole
source carrier has one context/count and the literal bytes of every
actual packet, with no repeated preparation or raw-index word. -/
theorem actual_carrier_lengths {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualCarrier r).word.length≤3*r.child.cellCall.seed.N^8*unitBudget r ∧
      (actualCarrier r).batchWord.length≤10*r.child.cellCall.seed.N^8*unitBudget r ∧
      ((actualCarrier r).packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length≤
        r.child.cellCall.seed.N^8*unitBudget r := by
  let U:=unitBudget r
  let N:=r.child.cellCall.seed.N^8
  have hN : 1≤N:=StageLiftSourceCost.walkCount_pos r
  have hU : 1≤U := by dsimp only [U,unitBudget];omega
  have hNU : 1≤N*U:=Nat.mul_pos hN hU
  have hNle : N≤N*U:=Nat.le_mul_of_pos_right _ hU
  have hUle : U≤N*U:=Nat.le_mul_of_pos_left _ hN
  have hsmall:=small_source_costs r
  have hpre : (batchContext r).length≤U:=hsmall.1
  have hcount : (natWord N).length≤U:=hsmall.2.1
  have hraw:=StageMain.CallSize.flatMap_length_le StageFormulaMetadata.RawWalkPacket.word
    (actualCarrier r).packets U (by
      intro packet hp
      obtain ⟨index,rfl⟩:=List.mem_ofFn.mp hp
      have h:=sourcePacketBound_spec r index
      have hU':=sourcePacketBound_le_unit r
      change (StageLift.sourceWalkPacket r index).word.length≤U
      omega)
  have htag:=taggedPacketWords_length (actualCarrier r).packets
  have hlen : (actualCarrier r).packets.length=N := by simp only [actualCarrier,List.length_ofFn];rfl
  rw [hlen] at hraw htag
  have hin : (actualCarrier r).word.length=(batchContext r).length+(natWord N).length+
      ((actualCarrier r).packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length := by
    simp only [actualCarrier,RawCarrier.word,batchContext,List.length_ofFn,List.length_append]
    rfl
  have hout : (actualCarrier r).batchWord.length=2*(batchContext r).length+1+(natWord N).length+
      (taggedPacketWords (actualCarrier r).packets).length := by
    simp only [actualCarrier,RawCarrier.batchWord,batchContext,List.length_ofFn,List.length_append,frame_length]
    rfl
  refine ⟨?_,?_,hraw⟩
  · change _≤3*N*U
    nlinarith only [hin,hraw,hpre,hcount,hUle]
  · change _≤10*N*U
    nlinarith only [hout,htag,hraw,hpre,hcount,hNle,hUle,hNU]

/-- Step 3 and `prop:time`, paper/paper.tex: actual acquisition, one preparation copy, packet
tag/isolation loop and measured final framing have one linear census
charge. Raw input targets have already been normalized by the source. -/
theorem actual_frontSteps_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualCarrier r).frontSteps≤10000*r.child.cellCall.seed.N^8*unitBudget r := by
  let U:=unitBudget r
  let N:=r.child.cellCall.seed.N^8
  have hN : 1≤N:=StageLiftSourceCost.walkCount_pos r
  have hU : 1≤U := by dsimp only [U,unitBudget];omega
  have hNU : 1≤N*U:=Nat.mul_pos hN hU
  have hNle : N≤N*U:=Nat.le_mul_of_pos_right _ hU
  have hUle : U≤N*U:=Nat.le_mul_of_pos_left _ hN
  obtain ⟨hin,hout,hraw⟩:=actual_carrier_lengths r
  have hprefix:=(small_source_costs r).2.2
  exact RawCarrier.frontSteps_bound (actualCarrier r) N U
    (by simp only [actualCarrier,List.length_ofFn];rfl) hin hout hraw hprefix hNle hUle hNU

end NearQuarticWires.StageCompiledTerms
