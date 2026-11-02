import Proof.Quartic.StageCarrierEnvelope.Metadata
import Proof.Quartic.StagePrintContext.SourceCost

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the actual
carrier prefix adds just its two genuine binary-length reads to the
already paid compact original-source decoder. -/
theorem metadataReadSteps_eq {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    metadataReadSteps r=StagePrintContext.readSteps (prepared r)+
      30*natBitLength (StageLift.preparedWordOf r).length+
      30*natBitLength (r.child.cellCall.seed.N^8)+66 := by
  unfold metadataReadSteps StagePrint.Carrier.contextCost StagePrintContext.readSteps
  rw [prepared_word]
  let T:=StageMain.Compact.initializeCost r.child.call r.child.selected.1
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness)
    (StageLift.preparedWordOf r).length
  change 6+(30*natBitLength (StageLift.preparedWordOf r).length+32+1+
    (T+1+(30*natBitLength (r.child.cellCall.seed.N^8)+32)))=
    6+T+30*natBitLength (StageLift.preparedWordOf r).length+
      30*natBitLength (r.child.cellCall.seed.N^8)+66
  omega

/-- `prop:time`, paper/paper.tex: the
metadata prefix clock is cubic in only its actual finite preparation,
independently of every following compiled Terms entry. -/
theorem metadataReadSteps_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    metadataReadSteps r≤10^7*((StageLift.preparedWordOf r).length+1)^3 := by
  have hs:=StagePrintContext.readSteps_bound (prepared r)
  rw [prepared_word] at hs
  have hn:=original_arity_le r
  have hp:=NearCubicGates.Close.Dispatch.natBitLength_le_succ (StageLift.preparedWordOf r).length
  have hc:=walk_count_bits r
  have h1 : 1≤((StageLift.preparedWordOf r).length+1)^3 := Nat.one_le_pow _ _ (by omega)
  have h3 : (StageLift.preparedWordOf r).length+1≤((StageLift.preparedWordOf r).length+1)^3 :=
    Nat.le_self_pow (by decide) _
  rw [metadataReadSteps_eq]
  omega

/-- `prop:time`, paper/paper.tex: the actual
header reconstruction and binary column codec have a quadratic finite
preparation cost, without a numerical column-count factor. -/
theorem metadataBodySteps_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    metadataBodySteps r≤10^6*((StageLift.preparedWordOf r).length+1)^2 := by
  have hs:=StagePrintContext.baseHeaderCost_bound (prepared r)
  rw [prepared_word] at hs
  have hn:=original_arity_le r
  have h1 : 1≤((StageLift.preparedWordOf r).length+1)^2 := Nat.one_le_pow _ _ (by omega)
  have h2 : (StageLift.preparedWordOf r).length+1≤((StageLift.preparedWordOf r).length+1)^2 :=
    Nat.le_self_pow (by decide) _
  change metadataBodySteps r≤_
  unfold metadataBodySteps
  change StagePrint.Header.baseHeaderCost r.child.call r.child.selected.1 r.child.witness≤_ at hs
  omega

/-- `prop:time`, paper/paper.tex: the whole
actual source-language clock includes acquisition, all metadata arithmetic,
framing and every sequencing step at a cubic small-prefix bound. -/
theorem metadataSteps_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    metadataSteps r≤10^8*((StageLift.preparedWordOf r).length+1)^3 := by
  have hr:=metadataReadSteps_bound r
  have hb:=metadataBodySteps_bound r
  have h1 : 1≤((StageLift.preparedWordOf r).length+1)^3 := Nat.one_le_pow _ _ (by omega)
  have h23 : ((StageLift.preparedWordOf r).length+1)^2≤((StageLift.preparedWordOf r).length+1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  unfold metadataSteps
  omega

end NearQuarticWires.StageCarrierEnvelope
