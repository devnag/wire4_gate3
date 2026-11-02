import Proof.Quartic.StagePrintTuple.KernelState
import Proof.Quartic.StagePrintTuple.HistoryData
import Proof.Quartic.StagePrintTuple.Coefficient
import Proof.Quartic.StagePrintTuple.ReverseIndex

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: a monomial
boundary retains its actual Terms cursor and coefficient, literal
ascending occurrence support, earlier history and signed cut prefix. -/
structure MonomialData (V : ℕ) where
  termCursor : ℕ
  remaining : ℕ
  coefficient : ℤ
  order : List (Fin V)
  historyPrefix : List Bool
  output : List Bool

/-- `lem:print`, paper/paper.tex: the three
small monomial caches contain the genuine support packet, coefficient
input and actual fixed-field coefficient reply; native caches start blank. -/
def MonomialData.reverseData (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) (done : ℕ) : KernelData where
  termCursor := data.termCursor
  remaining := data.remaining
  caches := ![frame (listWord natWord (data.order.map Fin.val)),
    frame (CoefficientRequest.word ⟨r.stackWidth+1,data.coefficient⟩),
    CoefficientRequest.output ⟨r.stackWidth+1,data.coefficient⟩,[],[],[]]
  cacheHeads := ![(marks (natWord data.order.length)).length,0,0,0,0,0]
  history := data.historyPrefix++tupleHistory (r.stackWidth+1) r.toRowContext.nativeKids data.order done
  historyHead := data.historyPrefix.length+
    (tupleHistoryPrefix (r.stackWidth+1) r.toRowContext.nativeKids data.order done).length
  output := data.output
  stride := done*(r.rowDimension+1)
  children := 0
  tuples := (tupleFields r.toRowContext.nativeKids (processedSupport data.order done)).length
  reverseIndex := data.order.length-done
  supportCard := data.order.length

/-- `lem:print`, paper/paper.tex: the exact
reverse-loop state additionally retains the physically measured full
support-frame byte counter for its later finite cache erasure. -/
def MonomialData.reverseState (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done : ℕ) : WState (span+29) 32 :=
  ((data.reverseData r done).state span r).setv 26
    (frame (listWord natWord (data.order.map Fin.val))).length

/-- `lem:print`, paper/paper.tex: each reverse
boundary has the actual remaining support count, including zero at
completion; the measured cache length is a separate persistent register. -/
theorem MonomialData.reverseState_index (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) (span done : ℕ) :
    (data.reverseState r span done).val 15=data.order.length-done := by
  simp [MonomialData.reverseState,KernelData.state,MonomialData.reverseData]

/-- `lem:print`, paper/paper.tex: every genuine
callee work bank is blank in the literal reverse-loop boundary state. -/
theorem MonomialData.reverseState_blank (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done : ℕ) (p : Program) (hp : p.tapeCount ≤ span) :
    CallBlank p (kernelSite span p hp) (data.reverseState r span done) := by
  have h := (data.reverseData r done).state_blank span r p hp
  refine ⟨h.bank,h.heads,h.tally,h.tallyHead,h.guard,h.guardHead,h.ruler,h.rulerHead,?_⟩
  intro i
  have hi : (kernelSite span p hp).regs i≠26 := by
    fin_cases i <;> simp [kernelSite,kernelCallRegisters]
  simpa only [MonomialData.reverseState,WState.setv_val,Function.update_of_ne hi] using h.registers i

end NearQuarticWires.StageTuple
