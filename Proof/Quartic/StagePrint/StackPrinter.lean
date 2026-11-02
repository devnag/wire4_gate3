import Proof.Quartic.StagePrint.StackSetup

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the serialized tuple-field count is exact. -/
theorem stackNums_length (r : StackRequest) :
    r.nums.length = r.tuples.length*(r.m*(r.s+1)) := by
  unfold StackRequest.nums
  rw [fieldNums_length (r.m*(r.s+1)),List.length_map]
  intro u hu
  obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hu
  have h:=flatten_take_length (r.s+1) ls ls.length (r.row_length ls hls) le_rfl
  rw [List.take_of_length_le le_rfl] at h
  rw [h,r.tuple_length ls hls]

/-- `lem:print`, paper/paper.tex: capacity covers extraction, arithmetic fields, dimensions, and complete cut output. -/
def StackRequest.capacity (r : StackRequest) : ℕ :=
  1+r.loadCapacity+(r.m*(r.s+1)+1)+(r.s+2)+(r.m+1)+(r.tuples.length+1)+
    ((r.nums.length+1)*(2*(r.W+1)+1)+2*r.nums.length+2*r.m+2*(r.m*(r.s+1))+
      r.tuples.length*(r.m*(r.s+1))+2*(r.s+1)+r.m*(r.s+1)+r.tuples.length+1+2*r.tuples.length)+
    (r.tuples.length*((r.s+2)*(2*(r.W+1)+1))+1)

/-- `lem:print`, paper/paper.tex: the complete output contains one stacked cut per tuple. -/
def StackRequest.output (r : StackRequest) : List Bool :=
  r.tuples.flatMap (cutRecs r.W r.s r.coefficient)

/-- `lem:print`, paper/paper.tex: one fixed program performs loading, dimension reads, and all stacking. -/
noncomputable def stackProgram : WMX 44 26 :=
  .seq stackLoadProgram (.seq stackDimensions (stackAll stackStreams stackRegisters))

/-- `lem:print`, paper/paper.tex: every physical preparation and arithmetic step is included. -/
def StackRequest.budget (r : StackRequest) : ℕ :=
  (r.loadCost+1+(r.loadCost+1+r.loadCost))+1+
    (r.dimensionCost+1+stackAllCost r.W (r.m*(r.s+1)) (r.s+1) r.m r.nums.length r.tuples.length)

/-- `lem:print`, paper/paper.tex: the cut constructor is valid from an ordinary cold serialized tuple input. -/
theorem stackProgram_spec (r : StackRequest) :
    Runs r.capacity stackProgram (idealStart 44 26 r.word r.lens) r.budget
      (fun τ => τ.st 44 = r.output) := by
  refine Runs.seqE (stackLoadProgram_spec r.capacity r) ?_
  refine Runs.seqE (stackDimensions_spec r.capacity r ?_ ?_ ?_ ?_) ?_
  all_goals try (unfold StackRequest.capacity;omega)
  have h:=stackAll_spec stackStreams stackRegisters r.capacity r.W r.s r.m r.nums
    r.coefficient r.ready 0 r.tuples [] [] r.tuple_length r.row_length
    (tupleAt_fieldNums r.m (r.s+1) r.tuples r.tuple_length r.row_length)
    (by rw [stackNums_length]) r.fields_fit r.stack_fit r.width_pos (stackReady_pre r)
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [StackRequest.ready,StackRequest.loaded,stackRegisters])
    (by simp [OutOn,StackRequest.ready,StackRequest.loaded,StackRequest.lens,stackStreams,stackRegisters,
      StablePartition.Workspace.overlay])
    (by unfold StackRequest.capacity;omega)
    (by simp only [List.length_nil,zero_add];unfold StackRequest.capacity;omega)
  exact h.post fun τ ht => by
    rcases ht.2.1 with ⟨hout,_,_⟩
    simpa [StackRequest.output,stackStreams,StablePartition.Workspace.overlay] using hout

/-- `lem:print`, paper/paper.tex: exact signed tuple stacking as a physical word function. -/
noncomputable def stackPrinter :
    WordFunction StackRequest StackRequest.word StackRequest.output (fun r=>2*r.budget+2) :=
  wordFunction_of_ideal stackProgram (44 : Fin 45) (by decide)
    StackRequest.capacity StackRequest.lens StackRequest.budget
    (fun _=>le_rfl) (fun r=>⟨by rfl,stackProgram_spec r⟩)

end NearQuarticWires.StagePrint
