import Proof.Quartic.StagePrintTuple.KernelMonomialSource
import Proof.Quartic.StagePrintTuple.MonomialPrepare
import Proof.Quartic.StagePrintTuple.ReverseLoop
import Proof.Quartic.StagePrintTuple.MonomialFinishContract
import Proof.Quartic.StagePrintTuple.TermStageContract

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: one actual
monomial has additive source-local, preparation, genuine reverse-loop
and final Stack/cleanup clocks, including three sequence transitions. -/
def termStageCost (B : StageNativeKids.NativeKidsRequest→ℕ)
    (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) : ℕ :=
  let support := (r.terms[k].1.sort (·≤·)).map Fin.val
  let coefficient := r.terms[k].2
  let data := r.progressMonomial k hk
  monomialAcquireCost (monomialLocalCapacity (r.stackWidth+1) support coefficient)
    (r.stackWidth+1) support coefficient+1+
    (monomialPrepareCost (r.stackWidth+1) support coefficient+1+
      (reverseLoopCost B r data+1+
        100000000*monomialFinishMagnitude r data r.terms[k] (List.getElem_mem hk)))

/-- `prop:time`, paper/paper.tex: analysis
capacity covers the actual finite subroutine bounds and real output
counter. Earlier output size appears only in capacity, not the clock. -/
def termStageCapacity (B : StageNativeKids.NativeKidsRequest→ℕ)
    (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) : ℕ :=
  let support := (r.terms[k].1.sort (·≤·)).map Fin.val
  let coefficient := r.terms[k].2
  let data := r.progressMonomial k hk
  monomialLocalCapacity (r.stackWidth+1) support coefficient+
    monomialPrepareCapacity (r.stackWidth+1) support coefficient+
    reverseLoopCapacity B r data+
    100000000*(monomialFinishMagnitude r data r.terms[k] (List.getElem_mem hk)+data.output.length+1)

end NearQuarticWires.StageTuple
