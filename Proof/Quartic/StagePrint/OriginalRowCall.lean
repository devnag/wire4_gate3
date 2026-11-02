import Proof.Quartic.StagePrint.OriginalRowDock
import Proof.Quartic.Cells.ParametersPrintOriginalFieldFit

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.ThresholdCompiler
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: every actual original child fits the exact physical signed fields already emitted by its compiler. -/
theorem OriginalRowData.fields_fit (r : OriginalRowData) :
    ∀z∈kidL r.child,SInt.encS z<2^(r.original.W+1) := by
  apply Cells.ParameterArithmetic.originalChild_compile_fields_fit r.original
  rw [show compileL r.original.weights r.original.target=(exactChildren r.gate).map kidL from
    originalChildRequest_children _ _ _]
  exact List.mem_map.mpr ⟨r.child,List.getElem_mem r.index.isLt,rfl⟩

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual affine-row request has no additional field-fit premise or widened child encoding. -/
def OriginalRowData.canonicalPullback (r : OriginalRowData) : StagePullback.RowRequest :=
  r.pullback r.fields_fit

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the physical metadata and selected original row are exactly the complete canonical affine request. -/
theorem OriginalRowData.canonicalPullback_word (r : OriginalRowData) :
    r.header r.fields_fit++recBits r.original.W
      (compileL r.original.weights r.original.target)[r.compilerIndex.val]=r.canonicalPullback.word :=
  r.pullbackWord r.fields_fit

/-- `imp:pullback`, paper/paper.tex: the actual affine row printer's signed input width is the original compiler's unchanged width plus its sign bit. -/
theorem OriginalRowData.canonicalPullback_Lin (r : OriginalRowData) :
    r.canonicalPullback.Lin=r.original.W+1 := rfl

end NearQuarticWires.StagePrint
