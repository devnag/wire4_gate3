import Proof.Quartic.StageCarrierEnvelope.Data
import Proof.Gates.CounterMachine.PrefixFinal
import Proof.Gates.Expand.Cost2

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.CounterMachine.PrefixProg

/-- `prop:time`, paper/paper.tex: only the
leading finite preparation length controls arithmetic allocation, never
the following possibly exponential compiled carrier length. -/
def metadataSizes : Sz := ⟨1000,2,0,0,0,0⟩

/-- `lem:print`, paper/paper.tex: allocation
reads the actual first binary field of the unchanged cold carrier. -/
theorem carrier_header {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    leadOnes (StagePrint.TermsCarrier.word r)=natBitLength (StageLift.preparedWordOf r).length := by
  unfold StagePrint.TermsCarrier.word
  simp only [List.append_assoc]
  exact leadOnes_natWord _ _

/-- `prop:time`, paper/paper.tex: the actual
metadata width covers the finite original source and its small geometry,
while remaining independent of every later Terms payload. -/
theorem metadata_width {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    100*((StageLift.preparedWordOf r).length+1)^2≤
      metadataSizes.W (leadOnes (StagePrint.TermsCarrier.word r)) := by
  rw [carrier_header]
  have hp : (StageLift.preparedWordOf r).length+1≤2^natBitLength (StageLift.preparedWordOf r).length :=
    lt_natBitLength _
  have hpow:=Nat.pow_le_pow_left hp 2
  rw [←pow_mul,Nat.mul_comm (natBitLength (StageLift.preparedWordOf r).length)] at hpow
  change 100*((StageLift.preparedWordOf r).length+1)^2≤
    2^(2*natBitLength (StageLift.preparedWordOf r).length)*1000
  nlinarith only [hpow]

/-- `lem:print`, paper/paper.tex: original
arity is bounded by the actual finite preparation, with no new size field. -/
theorem original_arity_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.call.n≤(StageLift.preparedWordOf r).length := by
  have hh:=StagePrintContext.arity_le_source (prepared r)
  rwa [prepared_word] at hh

/-- `prop:time`, paper/paper.tex: the binary
walk count is small in bit length; no loop scans its numerical value. -/
theorem walk_count_bits {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    natBitLength (r.child.cellCall.seed.N^8)≤4*r.child.call.n+2 := by
  have hb:=StageLiftSourceCost.walkCount_le r
  have hh:=NearCubicGates.Close.Expand.Layout.nbl_le_of_lt _ _
    (hb.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))
  have hk:=(Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).k_lt_n
  change r.child.selected.1.k<r.child.call.n at hk
  omega

end NearQuarticWires.StageCarrierEnvelope
