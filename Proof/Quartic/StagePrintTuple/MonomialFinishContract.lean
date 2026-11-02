import Proof.Quartic.StagePrintTuple.ReverseState
import Proof.Quartic.StagePrintTuple.Monomial
import Proof.Quartic.StagePrintTuple.StackContract
import Proof.Quartic.StagePrintTuple.KernelMaps

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.Tabulator
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: after one
complete monomial, its exact signed cut stream is appended and the
next real empty-tuple history segment is selected; all finite monomial
caches and local tuple/support counters are reusable and blank. -/
def MonomialData.finishedData (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms) : KernelData where
  termCursor := data.termCursor
  remaining := data.remaining
  caches := fun _=>[]
  cacheHeads := fun _=>0
  history := (data.reverseData r data.order.length).history++[false]
  historyHead := (data.reverseData r data.order.length).history.length
  output := data.output++(r.stackRequest t ht).output
  stride := 0
  children := 0
  tuples := 0
  reverseIndex := 0
  supportCard := 0

/-- `prop:time`, paper/paper.tex: one actual
post-reverse Stack/call/cleanup stage pays its small coefficient and
support caches, current tuple input and genuine Stack machine budget.
Earlier source, tuple history and cut prefixes are not multiplied in. -/
def monomialFinishMagnitude (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms) : ℕ :=
  let sr := r.stackRequest t ht
  stackInputMagnitude sr+sr.word.length+(2*sr.budget+2)+
    ((data.reverseData r data.order.length).caches 0).length+
    ((data.reverseData r data.order.length).caches 1).length+
    ((data.reverseData r data.order.length).caches 2).length+10

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete actual post-reverse monomial subprogram
formats and invokes the genuine Stack printer, appends its raw reply,
clears only finite measured caches and selects the next real history
segment. Its runtime bound excludes all earlier output/history bytes. -/
abbrev MonomialFinishSpec
    (program : (span : ℕ)→stackRecordPrinter.program.tapeCount ≤ span→WMX (span+29) 32) : Prop :=
  ∀ (span : ℕ) (hp : stackRecordPrinter.program.tapeCount ≤ span)
    (cap : ℕ) (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ)
    (ht : t∈r.terms),
    data.order=t.1.sort (·≤·) → data.coefficient=t.2 →
    100000000*(monomialFinishMagnitude r data t ht+data.output.length+1) ≤ cap →
    ∃τ,WXExec cap (program span hp) (data.reverseState r span data.order.length) τ
      (100000000*monomialFinishMagnitude r data t ht) ∧
        SimW ((data.finishedData r t ht).state span r) τ

end NearQuarticWires.StageTuple
