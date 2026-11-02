import Proof.Quartic.StagePrintTuple.KernelLayout
import Proof.Quartic.StagePrintTuple.SetupContract
import Proof.Quartic.StagePrintTuple.CallInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: the actual
prepared source loader retains its finite word and eleven exact fields
on the same literal thirteen source tapes. -/
def TermCutRequest.preparedLoadedSource (r : TermCutRequest) : Fin 13→List Bool :=
  ![frame r.preparedWord,r.preparedWord,r.preparedFields 0,r.preparedFields 1,
    r.preparedFields 2,r.preparedFields 3,r.preparedFields 4,r.preparedFields 5,
    r.preparedFields 6,r.preparedFields 7,r.preparedFields 8,r.preparedFields 9,r.preparedFields 10]

/-- `lem:print`, paper/paper.tex: a boundary
state records the actual Terms cursor, six finite caches, append-only
tuple history, signed cut output and five computed monomial counters. -/
structure KernelData where
  termCursor : ℕ
  remaining : ℕ
  caches : Fin 6→List Bool
  cacheHeads : Fin 6→ℕ
  history : List Bool
  historyHead : ℕ
  output : List Bool
  stride : ℕ
  children : ℕ
  tuples : ℕ
  reverseIndex : ℕ
  supportCard : ℕ

/-- `lem:print`, paper/paper.tex: the fixed
literal tape state retains actual source bytes before all cache/history
storage and leaves every reusable callee bank genuinely blank. -/
def KernelData.state (data : KernelData) (span : ℕ) (r : TermCutRequest) : WState (span+29) 32 where
  st := fun i=>if h:i.val < 13 then r.preparedLoadedSource ⟨i.val,h⟩ else
    if h:14 ≤ i.val ∧ i.val < 20 then data.caches ⟨i.val-14,by omega⟩ else
    if i.val=20 then data.history else if i.val=21 then data.output else []
  sh := fun i=>if i.val=5 then data.termCursor else
    if i.val=6 then (natWord (r.stackWidth+1)).length else
    if i.val=9 then (natWord (r.rowDimension+1)).length else
    if h:14 ≤ i.val ∧ i.val < 20 then data.cacheHeads ⟨i.val-14,by omega⟩ else
    if i.val=20 then data.historyHead else if i.val=21 then data.output.length else 0
  val := fun i=>if i.val=10 then r.stackWidth+1 else if i.val=11 then r.rowDimension+1 else
    if i.val=12 then data.stride else if i.val=13 then data.children else
    if i.val=14 then data.tuples else if i.val=15 then data.reverseIndex else
    if i.val=16 then data.supportCard else if i.val=17 then data.remaining else
    if i.val=18 then data.output.length else 0
  cell := false

/-- `lem:print`, paper/paper.tex: every actual
callee bank tape is blank at a main-controller boundary, independently
of the retained original source, caches or cumulative tuple history. -/
theorem KernelData.state_bank (data : KernelData) (span : ℕ) (r : TermCutRequest)
    (p : Program) (hp : p.tapeCount ≤  span) (j : Fin p.tapeCount) :
    (data.state span r).st ((kernelSite span p hp).bank j)=[] ∧
      (data.state span r).sh ((kernelSite span p hp).bank j)=0 := by
  have h0 : ¬30+j.val < 13 := by omega
  have h1 : ¬(14 ≤ 30+j.val ∧ 30+j.val < 20) := by omega
  have h5 : 30+j.val≠5 := by omega
  have h6 : 30+j.val≠6 := by omega
  have h9 : 30+j.val≠9 := by omega
  have h20 : 30+j.val≠20 := by omega
  have h21 : 30+j.val≠21 := by omega
  simp [KernelData.state,kernelSite,kernelBank,h0,h1,h5,h6,h9,h20,h21]

/-- `lem:print`, paper/paper.tex: the complete
cold-call invariant follows from the literal boundary layout and its
fixed zero call-scratch registers. -/
theorem KernelData.state_blank (data : KernelData) (span : ℕ) (r : TermCutRequest)
    (p : Program) (hp : p.tapeCount ≤  span) :
    CallBlank p (kernelSite span p hp) (data.state span r) := by
  refine ⟨fun j=>(data.state_bank span r p hp j).1,
    fun j=>(data.state_bank span r p hp j).2,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [KernelData.state,kernelSite,kernelLocal]
  · simp [KernelData.state,kernelSite,kernelLocal]
  · simp [KernelData.state,kernelSite,kernelLocal]
  · simp [KernelData.state,kernelSite,kernelLocal]
  · simpa [KernelData.state,kernelSite,kernelLocal] using
      (Control.nil_blank : NearCubicGates.Close.Worker.Blank [])
  · simp [KernelData.state,kernelSite,kernelLocal]
  · intro i
    fin_cases i  <;> simp [KernelData.state,kernelSite,kernelCallRegisters]

end NearQuarticWires.StageTuple
