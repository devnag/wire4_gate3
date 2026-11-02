import Proof.Quartic.StagePrint.OriginalChildMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.WordPrograms.SInt (encS SNumOn)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

/-- `lem:print`, paper/paper.tex: the signed compiler has distinct weight, target, output and constant streams. -/
def originalCompilerStreams : Fin 24 ↪ Fin 45 :=
  ⟨![2,7,43,44,8,9,10,11,12,18,20,3,21,22,23,24,25,31,33,34,5,4,35,36],by decide⟩

/-- `lem:print`, paper/paper.tex: the twenty-four compiler registers remain distinct from the dimension-reader scratch register. -/
def originalCompilerRegs : Fin 24 ↪ Fin 25 :=
  ⟨fun i=>⟨i.val,by have:=i.isLt;omega⟩,by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x:Fin 25=>x.val) h⟩

/-- `lem:print`, paper/paper.tex: the ready state retains original coefficients and reads only the original arity. -/
def OriginalChildRequest.ready (r : OriginalChildRequest) : WState 44 25 :=
  (r.loaded 3).setv 13 r.weights.length

/-- `lem:print`, paper/paper.tex: the compiler's input capacity includes every emitted original exact child. -/
def OriginalChildRequest.capacity (r : OriginalChildRequest) : ℕ :=
  r.loadCapacity + (compRecs r.W r.weights r.target).length +
    (r.weights.length+1)*(2*(r.W+1)+1)+2*r.weights.length+4*r.W+20

/-- `lem:print`, paper/paper.tex: every initialized signed work field has the exact common width. -/
theorem originalReady_pre (r : OriginalChildRequest) :
    CompPre originalCompilerStreams originalCompilerRegs r.capacity r.W r.ready := by
  constructor
  · intro k hk
    by_cases he:k=11
    · subst k
      exact ⟨encS r.target,by constructor <;> rfl⟩
    · fin_cases k <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hk <;>
        try contradiction
      all_goals exact ⟨0,by constructor <;> rfl⟩
  · rfl
  · simp [OriginalChildRequest.ready,OriginalChildRequest.loaded,originalCompilerStreams,
      OriginalChildRequest.lens]
  · constructor <;> rfl
  · constructor <;> rfl
  · intro k hk13 hk14
    simp [OriginalChildRequest.ready,OriginalChildRequest.loaded,originalCompilerRegs,
      Function.update_of_ne (show (⟨k.val,by have:=k.isLt;omega⟩:Fin 25) ≠ 13 by
        intro h
        apply hk13
        apply Fin.ext
        exact congrArg (fun x:Fin 25=>x.val) h)]
  · unfold OriginalChildRequest.capacity
    omega

/-- `lem:print`, paper/paper.tex: loading, dimension reading, and the original exact decomposition form one fixed physical program. -/
noncomputable def originalChildProgram : WMX 44 25 :=
  .seq (.mach NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadM (originalLoadMap 0))
  (.seq (.mach NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadM (originalLoadMap 1))
  (.seq (.mach NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadM (originalLoadMap 2))
  (.seq (unaryRegister 6 24 13) (compileP originalCompilerStreams originalCompilerRegs))))

/-- `lem:print`, paper/paper.tex: every field initialization and original-child operation is charged. -/
def OriginalChildRequest.budget (r : OriginalChildRequest) : ℕ :=
  r.loadCost+1+(r.loadCost+1+(r.loadCost+1+
    (16*r.weights.length+14+1+compileCost r.W r.weights.length)))

/-- `lem:print`, paper/paper.tex: the exact original-child record stream. -/
def OriginalChildRequest.output (r : OriginalChildRequest) : List Bool :=
  compRecs r.W r.weights r.target

/-- `lem:print`, paper/paper.tex: the original exact-child compiler starts from its sole encoded input. -/
theorem originalChildProgram_spec (r : OriginalChildRequest) :
    Runs r.capacity originalChildProgram (idealStart 44 25 r.word r.lens) r.budget
      (fun τ=>τ.st 43=r.output) := by
  rw [←originalLoad_zero]
  refine Runs.seqE (originalLoad_spec r.capacity r 0) ?_
  refine Runs.seqE (originalLoad_spec r.capacity r 1) ?_
  refine Runs.seqE (originalLoad_spec r.capacity r 2) ?_
  have hn:=unaryRegister_spec r.capacity (6:Fin 45) (24:Fin 25) 13 (by decide)
    (r.loaded 3) r.weights.length rfl rfl rfl rfl
    (by unfold OriginalChildRequest.capacity;omega)
  refine Runs.seqE hn ?_
  have hc:=compile_spec originalCompilerStreams originalCompilerRegs r.capacity r.W r.ready
    r.weights [] r.target [] [] (originalReady_pre r)
    ⟨0,by constructor <;> rfl⟩
    (by
      refine ⟨⟨rfl,rfl⟩,?_⟩
      have h:=r.target_fit
      omega)
    (by simp only [List.append_nil];rfl) rfl
    (by simp [OriginalChildRequest.ready,originalCompilerRegs])
    (by simp [OutOn,OriginalChildRequest.ready,OriginalChildRequest.loaded,
      originalCompilerStreams,originalCompilerRegs,OriginalChildRequest.lens,
      StablePartition.Workspace.overlay]) r.weights_fit r.target_fit
    (by simp only [List.length_nil,zero_add];unfold OriginalChildRequest.capacity;omega)
  exact hc.post fun τ h=>by
    rcases h.1 with ⟨ho,_,_⟩
    simpa [OriginalChildRequest.output,originalCompilerStreams,
      StablePartition.Workspace.overlay] using ho

/-- `lem:print`, paper/paper.tex: original disjoint exact children are constructed by an actual cold-input word function. -/
noncomputable def originalChildPrinter :
    WordFunction OriginalChildRequest OriginalChildRequest.word OriginalChildRequest.output
      (fun r=>2*r.budget+2) :=
  wordFunction_of_ideal originalChildProgram (43:Fin 45) (by decide)
    OriginalChildRequest.capacity OriginalChildRequest.lens OriginalChildRequest.budget
    (fun _=>le_rfl) (fun r=>⟨by rfl,originalChildProgram_spec r⟩)

end NearQuarticWires.StagePrint
