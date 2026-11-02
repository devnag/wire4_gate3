import Proof.Quartic.StagePrintTuple.ChildCounter
import Proof.Quartic.StagePrint.IndexedCallChildren
import Proof.Quartic.Program.Pipe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.TabMachine
open StagePrint

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the count input is precisely the ORIGINAL compiler's
actual child-record output, before any translated-corner pullback. -/
def originalCountRequest (r : OriginalChildRequest) : ChildCountRequest where
  records := (compileL r.weights r.target).map (recBits r.W)
  nonempty := by
    intro record hr
    obtain ⟨child,hchild,rfl⟩ := List.mem_map.mp hr
    have hl : (recBits r.W child).length=(r.weights.length+1)*(r.W+1) := by
      unfold recBits
      rw [List.length_flatMap]
      simp only [SignedSortKey.binary_length,List.map_const',List.sum_replicate,smul_eq_mul]
      rw [compileL_length _ _ child hchild]
    intro he
    have hz := congrArg List.length he
    rw [hl] at hz
    simp only [List.length_nil] at hz
    have hp : 0<(r.weights.length+1)*(r.W+1) := Nat.mul_pos (by omega) (by omega)
    omega

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: no intermediate record-list or output-length provider
is added between the real compiler and the real count machine. -/
theorem originalCountRequest_word (r : OriginalChildRequest) :
    (originalCountRequest r).word=r.output := by
  simp only [originalCountRequest,ChildCountRequest.word,OriginalChildRequest.output,
    compRecs,List.flatMap_map]

/-- `lem:print`, paper/paper.tex: the actual
computed count equals the ORIGINAL compiler's exact child census. -/
theorem originalCountRequest_count (r : OriginalChildRequest) :
    (originalCountRequest r).records.length=(compileL r.weights r.target).length := by
  simp only [originalCountRequest,List.length_map]

/-- `prop:time`, paper/paper.tex: original
compilation and actual record counting have additive physical costs. -/
noncomputable def indexedOriginalCountBudget {second : Bool}
    (r : RawBits.IndexedCallGateRequest second) : ℕ :=
  4*r.childrenBudget+4*(2*(originalCountRequest r.child).steps+2)+12

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: actual finite original-call bytes and occurrence index
produce the exact original-child count. Both subroutines are concrete
existing cold machines, with their real codec handoff proved exactly. -/
noncomputable def indexedOriginalCountPrinter (second : Bool) :
    WordFunction (RawBits.IndexedCallGateRequest second) RawBits.IndexedCallGateRequest.source
      (fun r=>frame (natWord (compileL r.child.weights r.child.target).length))
      indexedOriginalCountBudget := by
  let count : WordFunction (RawBits.IndexedCallGateRequest second)
      (fun r=>r.child.output)
      (fun r=>frame (natWord (compileL r.child.weights r.child.target).length))
      (fun r=>2*(originalCountRequest r.child).steps+2) :=
    ⟨childCounterWordFunction.program,by
      intro r
      simpa only [originalCountRequest_word,ChildCountRequest.output,originalCountRequest_count]
        using childCounterWordFunction.realizes (originalCountRequest r.child)⟩
  exact Program.WordFunction.pipe (RawBits.indexedCallChildren second) count

end NearQuarticWires.StageTuple
