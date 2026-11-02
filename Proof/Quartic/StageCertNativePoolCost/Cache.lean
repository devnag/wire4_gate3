import Proof.Quartic.StageCertNativePoolCost.Sources

set_option autoImplicit false

namespace NearQuarticWires.StageCertNativePoolCost

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCertNative StageCertificateControl

/-- `prop:time`, paper/paper.tex: the
actual first ordinal source retains and scans its original BASE,
including the literal ordinal writer and ordinary call costs. -/
theorem price_firstSourceBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>2*StageGamma.retainedCost
      (input:=IndexedRequest.baseWord) (cache:=fun _ : IndexedRequest B1 B2=>natWord 0)
      (budget:=zeroOrdinalBudget) j.base+2) 0 := by
  have hh:=((JobPrice.constant 2).mul (price_zeroOrdinalBudget B1 B2)).add
    ((JobPrice.constant 150).mul (((price_baseWordLength B1 B2).add
      (JobPrice.constant (natWord 0).length)).add (JobPrice.constant 1)))
  exact ((JobPrice.constant 2).mul hh).add (JobPrice.constant 2)

theorem price_basePrepBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>basePrepBudget j.base) 0 :=
  (((JobPrice.constant 4).mul (price_firstSourceBudget B1 B2)).add
    ((JobPrice.constant 4).mul (price_zeroPrepCopyBudget B1 B2))).add (JobPrice.constant 12)

theorem price_countBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>countBudget j.base) 0 :=
  (((JobPrice.constant 4).mul (price_firstSourceBudget B1 B2)).add
    ((JobPrice.constant 4).mul (price_countBodyBudget B1 B2))).add (JobPrice.constant 12)

/-- `prop:time`, paper/paper.tex: the
actual context producer is invoked once and priced by its original
finite prep, with no decoded-context or length premise. -/
theorem price_contextProducerBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>(StagePrintContext.contextProducer B1 B2).1 j.base.prepared) 0 := by
  refine ((JobPrice.constant (10^25)).mul
    (((price_prepLength B1 B2).add (JobPrice.constant 1)).pow 8)).mono ?_
  exact fun j=>StagePrintContext.contextBudget_bound j.base.prepared

theorem price_baseContextBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>baseContextBudget j.base) 0 :=
  (((JobPrice.constant 4).mul (price_basePrepBudget B1 B2)).add
    ((JobPrice.constant 4).mul (price_contextProducerBudget B1 B2))).add (JobPrice.constant 12)

theorem price_retainedContextBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>retainedContextBudget j.base) 0 := by
  have hh:=((JobPrice.constant 2).mul (price_baseContextBudget B1 B2)).add
    ((JobPrice.constant 150).mul (((price_baseWordLength B1 B2).add
      (price_contextLength B1 B2)).add (JobPrice.constant 1)))
  exact ((JobPrice.constant 2).mul hh).add (JobPrice.constant 2)

/-- `prop:time`, paper/paper.tex: every
actual cached-source byte, count calculation, context call and
framed-pair composition has occurrence exponent zero. -/
theorem price_cachedSourceBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>cachedSourceBudget j.base) 0 := by
  have hr : JobPrice (fun j : TermJob B1 B2=>
      (j.base.baseWord++StagePrint.Context.word j.base.prepared).length) 0 := by
    simpa only [List.length_append] using
      (price_baseWordLength B1 B2).add (price_contextLength B1 B2)
  exact (price_baseWordLength B1 B2).framedPair (price_countWordLength B1 B2) hr
    (price_countBudget B1 B2) (price_retainedContextBudget B1 B2)

/-- `prop:time`, paper/paper.tex: reading
the real cached binary count uses its exact finite compiler budget;
the possibly exponential count is charged only by codec width here. -/
theorem price_cachedCountBudget (B1 B2 : ℕ) :
    JobPrice (fun j : TermJob B1 B2=>cachedCountBudget j.base) 0 := by
  have hs:=((JobPrice.constant 70).mul (price_countBits B1 B2)).add (JobPrice.constant 80)
  exact (price_cachedSourceLength B1 B2).finite
    (((JobPrice.constant 3).mul hs).add (JobPrice.constant 8)) StageRecovery.packetCallee VV MM

end NearQuarticWires.StageCertNativePoolCost
