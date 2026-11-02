import Proof.Quartic.StageColumns.Metadata

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def columnScratch : List (Fin VV) := coordinateIndex :: bitScratch

def generatorScratch : List (Fin VV) := columnIndex :: columnScratch

/-- `imp:partition` and `lem:print`, paper/paper.tex: source dimensions remain unchanged during both actual
column enumeration loops. -/
theorem Prepared.frame {a b : DS VV MM} {P : StarParams}
    (h : Prepared a P) (hf : Fr a b generatorScratch) : Prepared b P :=
  ⟨h.constants.of_fr hf (by decide), (hf _ (by decide)).trans h.blockWidth,
    (hf _ (by decide)).trans h.parityWidth, (hf _ (by decide)).trans h.width,
    (hf _ (by decide)).trans h.dimension, (hf _ (by decide)).trans h.left,
    (hf _ (by decide)).trans h.data, (hf _ (by decide)).trans h.count⟩

/-- `imp:partition`, paper/paper.tex: the actual
loop counters and retained canonical dimensions supply each bit call. -/
theorem Prepared.bitInputs {a : DS VV MM} {P : StarParams} {j p : ℕ}
    (h : Prepared a P) (hj : a.env columnIndex = j) (hp : a.env coordinateIndex = p) :
    BitInputs a P j p :=
  ⟨h.constants, hj, hp, h.blockWidth, h.parityWidth, h.data, h.left, h.count⟩

end NearQuarticWires.StageColumns
