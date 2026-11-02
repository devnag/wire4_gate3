import Proof.Quartic.StageColumns.Division

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def bitScratch : List (Fin VV) :=
  divisionScratch ++ codewordScratch ++ [freePosition, result, vJ]

/-- `imp:partition`, paper/paper.tex: these scalar
registers are the actual canonical block dimensions and current
generator-column and half-coordinate indices. -/
structure BitInputs (a : DS VV MM) (P : StarParams) (j p : ℕ) : Prop where
  constants : Cst a
  column : a.env columnIndex = j
  coordinate : a.env coordinateIndex = p
  blockWidth : a.env 22 = P.b
  parityWidth : a.env 23 = P.s
  data : a.env dataWidth = PrimT.C4Geo.dB P
  left : a.env leftWidth = P.r / 2 * P.b
  count : a.env dataCount = P.r / 2 * PrimT.C4Geo.dB P

/-- `imp:partition` and `lem:print`, paper/paper.tex: every column-bit computation retains the source
parameters and the two actual enumeration counters. -/
theorem BitInputs.frame {a b : DS VV MM} {P : StarParams} {j p : ℕ}
    (h : BitInputs a P j p) (hf : Fr a b bitScratch) : BitInputs b P j p :=
  ⟨h.constants.of_fr hf (by decide), (hf _ (by decide)).trans h.column,
    (hf _ (by decide)).trans h.coordinate, (hf _ (by decide)).trans h.blockWidth,
    (hf _ (by decide)).trans h.parityWidth, (hf _ (by decide)).trans h.data,
    (hf _ (by decide)).trans h.left, (hf _ (by decide)).trans h.count⟩

end NearQuarticWires.StageColumns
