import Proof.Quartic.StageLiftMasks.Product

/-!
# Original eight-mask source machine

`def:mask`, `lem:print` and `prop:time`, paper/paper.tex: the fixed original
walk executes eight actual structural queries and the full guarded
tuple-mask enumeration, preserving the retained source and loop state.
The bound includes every query and the complete exponential enumeration.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

def printMasksProgram : St VV MM := printMaskList (List.ofFn fun edge : Fin 8=>edge)

theorem printMasksProgram_run : printMasksProgramSpec printMasksProgram := by
  intro B1 B2 width input L B r index a h
  obtain ⟨z,n,he,hn,zo,zr,zf⟩:=printMaskList_run input r index
    (List.ofFn fun edge : Fin 8=>edge) a h
  refine ⟨z,n,he,?_,?_,zf.records,zf.cursors,zf.input,zr.inputEmpty,zr.residue,zf.registers⟩
  · apply hn.trans
    simp only [List.length_ofFn]
    dsimp only [edgeCost,originalMaskCost,printMasksCost,completeMaskSourceCost]
    have hp : 1≤(sourceEnvelope r+1)^4 := Nat.one_le_pow _ _ (by omega)
    omega
  · rw [maskProductFormula_full] at zo
    exact zo

end NearQuarticWires.StageLiftMasks
