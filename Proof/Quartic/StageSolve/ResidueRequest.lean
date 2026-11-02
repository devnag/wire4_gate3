import Proof.Quartic.Walks.Residue
import Proof.Gates.Interfaces.CounterFormats
import Proof.Gates.Cells.Mac

set_option autoImplicit false

namespace NearQuarticWires.StageSolve

/-- `lem:residue`, paper/paper.tex: a modulus and one
already bounded integer value for the elementary centered-decoding program. -/
structure ResidueRequest where
  modulus : ℕ
  value : ℤ

/-- `lem:residue`, paper/paper.tex: the literal raw
modulus/integer codec of the elementary centered-decoding program. -/
def residueInput (r : ResidueRequest) : List Bool :=
  NearCubicWires.RepairRepresentation.natWord r.modulus ++
    NearCubicGates.Close.Interfaces.intWord r.value

/-- `lem:residue`, paper/paper.tex: the exact centered value
of the supplied bounded integer; modular printing supplies such values
without materializing the unbounded amplified polynomial. -/
def residueValue (r : ResidueRequest) : ℤ := Walks.centeredResidue (r.modulus : ℤ) r.value

end NearQuarticWires.StageSolve
