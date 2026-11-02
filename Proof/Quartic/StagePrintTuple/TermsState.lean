import Proof.Quartic.StagePrintTuple.MonomialFinishContract
import Proof.Quartic.StagePrintTuple.KernelInitialize

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the actual
monomial cursor follows its single original list-count codec and the
literal already consumed monomial bytes. -/
def TermCutRequest.termsPrefix (r : TermCutRequest) (k : ℕ) : List Bool :=
  natWord r.terms.length++(r.terms.take k).flatMap monoWord

/-- `lem:print`, paper/paper.tex: each original
monomial contributes its complete real suffix-tuple history exactly
once before the next empty-tuple segment. -/
def TermCutRequest.termHistory (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ) : List Bool :=
  tupleHistory (r.stackWidth+1) r.toRowContext.nativeKids (t.1.sort (·≤·)) t.1.card

/-- `lem:print`, paper/paper.tex: the actual
signed equality stream for one monomial retains its original tuple
and coefficient order before weak-cut conversion. -/
def TermCutRequest.termOutput (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ) : List Bool :=
  (r.monomialTuples t).flatMap (cutRecs r.stackWidth r.rowDimension t.2)

/-- `lem:print`, paper/paper.tex: the complete
Terms-loop boundary retains all source bytes once, an actual prefix
cursor, an append-only tuple history and exact signed cut prefix. -/
def TermCutRequest.progressData (r : TermCutRequest) (k : ℕ) : KernelData where
  termCursor := (r.termsPrefix k).length
  remaining := r.terms.length-k
  caches := fun _=>[]
  cacheHeads := fun _=>0
  history := (r.terms.take k).flatMap r.termHistory++[false]
  historyHead := ((r.terms.take k).flatMap r.termHistory).length
  output := (r.terms.take k).flatMap r.termOutput
  stride := 0
  children := 0
  tuples := 0
  reverseIndex := 0
  supportCard := 0

/-- `lem:print`, paper/paper.tex: after real
source acquisition, the monomial state records precisely the next
Terms cursor, decremented actual count and unchanged earlier prefixes. -/
def TermCutRequest.progressMonomial (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) :
    MonomialData (17*(Builder.allGates r.header.call).length) where
  termCursor := (r.termsPrefix (k+1)).length
  remaining := r.terms.length-(k+1)
  coefficient := r.terms[k].2
  order := r.terms[k].1.sort (·≤·)
  historyPrefix := (r.terms.take k).flatMap r.termHistory
  output := (r.terms.take k).flatMap r.termOutput

/-- `lem:print`, paper/paper.tex: physical
initialization is exactly the zero-term progress boundary. -/
theorem TermCutRequest.progressData_zero (r : TermCutRequest) :
    r.progressData 0=kernelInitialData r := by
  simp [TermCutRequest.progressData,TermCutRequest.termsPrefix,kernelInitialData]

/-- `lem:print`, paper/paper.tex: at complete
progress the stored cut prefix is exactly the requested equality stream. -/
theorem TermCutRequest.progressData_output (r : TermCutRequest) :
    (r.progressData r.terms.length).output=r.output := by
  change (r.terms.take r.terms.length).flatMap r.termOutput=r.output
  rw [List.take_length]
  rfl

/-- `lem:print`, paper/paper.tex: finishing the
genuine current monomial advances exactly one full Terms boundary,
including its actual byte cursor, tuple history and signed cut prefix. -/
theorem TermCutRequest.progress_finished (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) :
    ((r.progressMonomial k hk).finishedData r r.terms[k] (List.getElem_mem hk))=
      r.progressData (k+1) := by
  have hp := List.take_succ_eq_append_getElem hk
  have hlen : (r.terms[k].1.sort (·≤·)).length=r.terms[k].1.card := by
    simp only [Finset.length_sort]
  simp only [MonomialData.finishedData,TermCutRequest.progressMonomial,
    MonomialData.reverseData,TermCutRequest.progressData,TermCutRequest.stackRequest,
    StagePrint.StackRequest.output,KernelData.mk.injEq]
  refine ⟨by trivial,by trivial,by trivial,by trivial,?_,?_,?_,by trivial,by trivial,
    by trivial,by trivial,by trivial⟩
  · rw [hp,List.flatMap_append,List.flatMap_singleton]
    simp [TermCutRequest.termHistory,hlen,List.append_assoc]
  · rw [hp,List.flatMap_append,List.flatMap_singleton,List.length_append]
    simp [TermCutRequest.termHistory,hlen]
  · rw [hp,List.flatMap_append,List.flatMap_singleton]
    rfl

end NearQuarticWires.StageTuple
