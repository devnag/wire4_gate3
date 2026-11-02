import Proof.Quartic.StageCompiledTerms.UnitBudget
import Proof.Quartic.StageCompiledTerms.Frontend

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairRepresentation
open StageLiftSourceCost

/-- Step 3 and `prop:time`, paper/paper.tex: the one original preparation context, encoded walk
census and their actual decoder/copy work fit the paid packet scale. -/
theorem small_source_costs {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (batchContext r).length≤unitBudget r ∧
      (natWord (r.child.cellCall.seed.N^8)).length≤unitBudget r ∧
      prefixCost (StageLift.preparedWordOf r) (r.child.cellCall.seed.N^8)≤unitBudget r := by
  let S:=sourceScale r
  let P:=(StageLift.preparedWordOf r).length
  let N:=r.child.cellCall.seed.N^8
  have hS : 1≤S := by have h:=(sourceScale_small r).1;omega
  have hP : P≤S:=(source_word_lengths r).1
  have hE : StageLift.sourceEnvelope r+1≤S:=(sourceScale_small r).2.1
  have hB:=StageLift.source_walk_counter_bits r
  have hpbits:=NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self P
  have hpow:=NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le P
  have hnword : (natWord N).length≤20*(S+1) := by
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
    change natBitLength N≤8*StageLift.sourceEnvelope r+1 at hB
    omega
  have hpword : (natWord P).length≤3*(S+1) := by
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
    omega
  have hcontext : (batchContext r).length≤4*(S+1) := by
    change (natWord P++StageLift.preparedWordOf r).length≤_
    rw [List.length_append]
    change (natWord P).length+P≤_
    omega
  have hclock : prefixCost (StageLift.preparedWordOf r) N≤10^6*(S+1)^3 := by
    unfold prefixCost StagePacket.payloadLengthCost
    change (natBitLength P+2)*(40*2^natBitLength P+40)+60*P+36*natBitLength P+73+
      100*((natWord P).length+P+(natWord N).length+1)≤_
    have hp : natBitLength P≤S+1:=hpbits.trans (by omega)
    have h2 : 2^natBitLength P≤2*(S+1):=hpow.trans (Nat.mul_le_mul_left _ (by omega))
    have hprod:=Nat.mul_le_mul (show natBitLength P+2≤S+3 by omega)
      (show 40*2^natBitLength P+40≤80*(S+1)+40 by omega)
    calc _≤(S+3)*(80*(S+1)+40)+60*S+36*(S+1)+73+
        100*(3*(S+1)+S+20*(S+1)+1) := by nlinarith only [hprod,hP,hp,hnword,hpword]
      _≤10000*(S+1)^2 := by nlinarith
      _≤10000*(S+1)^3:=Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (by decide))
      _≤10^6*(S+1)^3:=Nat.mul_le_mul_right _ (by decide)
  have hscale:=(sourcePacketBound_small_overhead r).trans (sourcePacketBound_le_unit r)
  change 10^6*(S+1)^3≤unitBudget r at hscale
  have hbase : S+1≤(S+1)^3:=Nat.le_self_pow (by decide) _
  exact ⟨hcontext.trans (by nlinarith only [hscale,hbase]),
    hnword.trans (by nlinarith only [hscale,hbase]),hclock.trans hscale⟩

end NearQuarticWires.StageCompiledTerms
