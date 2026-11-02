import Proof.Quartic.StagePrint.IndexedCallChildren
import Proof.Quartic.StagePrint.OriginalNativeRow
import Proof.Quartic.StagePrint.RowSelectorInput
import Proof.Quartic.StagePrint.PullbackInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.TabMachine

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: one original occurrence and original child index, with actual affine metadata; no decoded child list or row is an input. -/
structure OriginalPipelineRequest (second : Bool) where
  source : RawBits.IndexedCallGateRequest second
  suffix_empty : source.suffix=[]
  row : OriginalRowData
  original_eq : row.original=source.child

/-- `lem:print`, paper/paper.tex: the on-demand occurrence compiler is the existing actual cold original-call machine, reindexed only by its retained metadata. -/
noncomputable def pipelineChildren (second : Bool) :
    WordFunction (OriginalPipelineRequest second) (fun r=>r.source.source)
      (fun r=>frame r.row.original.output) (fun r=>r.source.childrenBudget) :=
  ⟨(RawBits.indexedCallChildren second).program,by
    intro r
    simpa only [r.original_eq] using (RawBits.indexedCallChildren second).realizes r.source⟩

/-- `lem:print`, paper/paper.tex: the original row selector retains the compiler's exact occurrence and child order. -/
noncomputable def pipelineSelector (second : Bool) :
    WordFunction (OriginalPipelineRequest second)
      (fun r=>(originalRowRequest r.row.original r.row.compilerIndex).word)
      (fun r=>frame (recBits r.row.original.W
        (compileL r.row.original.weights r.row.original.target)[r.row.compilerIndex.val]))
      (fun r=>2*(originalRowRequest r.row.original r.row.compilerIndex).lower.budget+2) :=
  ⟨originalRowSelector.program,fun r=>originalRowSelector.realizes ⟨r.row.original,r.row.compilerIndex⟩⟩

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the final cold machine is the actual same-center signed affine-row printer. -/
noncomputable def pipelinePullback (second : Bool) :
    WordFunction (OriginalPipelineRequest second) (fun r=>r.row.canonicalPullback.word)
      (fun r=>r.row.canonicalPullback.output) (fun r=>StagePullback.rowCost r.row.canonicalPullback) :=
  ⟨StagePullback.rowWordFunction.program,fun r=>StagePullback.rowWordFunction.realizes r.row.canonicalPullback⟩

/-- `lem:print`, paper/paper.tex: the original source, unary original-child index and actual affine header are three separately framed input fields. -/
def OriginalPipelineRequest.word {second : Bool} (r : OriginalPipelineRequest second) : List Bool :=
  Top.loadRec (frame r.source.source) (frame (List.replicate r.row.compilerIndex.val true))
    (frame (r.row.header r.row.fields_fit)) [] [] [] [] [] [] [] []

/-- `prop:time`, paper/paper.tex: actual loading of every original-source, index and metadata bit is included. -/
def OriginalPipelineRequest.loadCost {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  Top.loadCost (frame r.source.source) (frame (List.replicate r.row.compilerIndex.val true))
    (frame (r.row.header r.row.fields_fit)) [] [] [] [] [] [] [] []

/-- `prop:time`, paper/paper.tex: the physical input extractor has its ordinary explicit blank-ruler capacity. -/
def OriginalPipelineRequest.loadCapacity {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  2*r.word.length+1+Top.loadChainCost (frame r.source.source)
    (frame (List.replicate r.row.compilerIndex.val true)) (frame (r.row.header r.row.fields_fit))
      [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the exact source fields after the actual eleven-field loader. -/
def OriginalPipelineRequest.fields {second : Bool} (r : OriginalPipelineRequest second) : Fin 13→List Bool :=
  ![frame r.word,r.word,frame r.source.source,frame (List.replicate r.row.compilerIndex.val true),
    frame (r.row.header r.row.fields_fit),[],[],[],[],[],[],[],[]]

/-- `lem:print`, paper/paper.tex: the three ordinary subroutine tape banks are fixed independently of all input values. -/
noncomputable def firstTapes (second : Bool) :=(pipelineChildren second).program.tapeCount
noncomputable def selectTapes :=originalRowSelector.program.tapeCount
noncomputable def pullTapes :=StagePullback.rowWordFunction.program.tapeCount
noncomputable def pipelineStreams (second : Bool) :=18+firstTapes second+selectTapes+pullTapes

/-- `lem:print`, paper/paper.tex: the actual loader occupies only its fixed fourteen tapes. -/
def pipelineLoadMap (second : Bool) (j : Fin 14) : Fin (pipelineStreams second+1):=
  ⟨j.val,by have:=j.isLt;unfold pipelineStreams;omega⟩

/-- `lem:print`, paper/paper.tex: the first ordinary machine reads directly from the physically loaded original-source field. -/
noncomputable def firstMap (second : Bool) (j : Fin (firstTapes second)) : Fin (pipelineStreams second+1):=
  if j.val=0 then ⟨2,by unfold pipelineStreams;omega⟩ else ⟨14+j.val,by have:=j.isLt;unfold pipelineStreams;omega⟩

/-- `lem:print`, paper/paper.tex: the first call ruler is disjoint from the source, index, header and all three machine banks. -/
noncomputable def firstRuler (second : Bool) : Fin (pipelineStreams second+1):=
  ⟨14+firstTapes second,by unfold pipelineStreams;omega⟩

/-- `lem:print`, paper/paper.tex: the selector has its own fixed bank and real serialized input tape. -/
noncomputable def selectMap (second : Bool) (j : Fin selectTapes) : Fin (pipelineStreams second+1):=
  ⟨15+firstTapes second+j.val,by have:=j.isLt;unfold pipelineStreams;omega⟩

/-- `lem:print`, paper/paper.tex: the selector ruler is outside its tape bank. -/
noncomputable def selectRuler (second : Bool) : Fin (pipelineStreams second+1):=
  ⟨15+firstTapes second+selectTapes,by unfold pipelineStreams;omega⟩

/-- `lem:print`, paper/paper.tex: the pullback has a third distinct tape bank, so no child selector can overwrite its header. -/
noncomputable def pullMap (second : Bool) (j : Fin pullTapes) : Fin (pipelineStreams second+1):=
  ⟨16+firstTapes second+selectTapes+j.val,by have:=j.isLt;unfold pipelineStreams;omega⟩

/-- `lem:print`, paper/paper.tex: the actual pullback ruler is outside every preceding source and machine tape. -/
noncomputable def pullRuler (second : Bool) : Fin (pipelineStreams second+1):=
  ⟨16+firstTapes second+selectTapes+pullTapes,by unfold pipelineStreams;omega⟩

/-- `lem:print`, paper/paper.tex: all ordinary-machine embeddings are genuinely injective. -/
theorem pipelineMap_injective (second : Bool) :
    Function.Injective (firstMap second) ∧ Function.Injective (selectMap second) ∧
      Function.Injective (pullMap second) ∧ Function.Injective (pipelineLoadMap second) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i j h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    unfold firstMap at hv
    split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> omega
  · intro i j h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    simp only [selectMap,Fin.val_mk] at hv
    omega
  · intro i j h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    simp only [pullMap,Fin.val_mk] at hv
    omega
  · intro i j h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    simpa only [pipelineLoadMap,Fin.val_mk] using hv

end NearQuarticWires.StagePrint
