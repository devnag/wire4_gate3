import Proof.Quartic.StageLift.ParameterFields
import Proof.Quartic.StageLift.ListFields

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:params`, paper/paper.tex: the retained
scalar fields, sorted primes and factors occupy separate record stores. -/
def parameterStore : Fin MM := 0
def primeStore : Fin MM := 1
def factorStore : Fin MM := 2

/-- `sec:params`, paper/paper.tex: counted list
lengths are kept outside every natural-reader scratch field. -/
def primeCountVar : Fin VV := ⟨121, by decide⟩
def factorCountVar : Fin VV := ⟨122, by decide⟩

/-- `sec:params` and `lem:print`, paper/paper.tex: the fixed complete parameter parser reads its two
scalar blocks and its two actual counted list payloads. -/
def readParameters : St VV MM :=
  .seq (readFixedFields parameterStore 37)
    (.seq (readListFields primeStore primeCountVar)
      (.seq (readFixedFields parameterStore 9) (readListFields factorStore factorCountVar)))

/-- `sec:params` and `lem:print`, paper/paper.tex: every decoded scalar follows the public parameter
record order, with both list lengths retained separately. -/
def parameterScalars (p : Cells.Parameters) : List ℕ :=
  parameterHeadScalars p ++ parameterTailScalars p

/-- `sec:params` and `prop:time`, paper/paper.tex: the parser charges actual scalar bit lengths and
linear counted-payload work at the common bit bound. -/
def parameterReadCost (p : Cells.Parameters) (B : ℕ) : ℕ :=
  (30 * ((parameterHeadScalars p).map natBitLength).sum + 34 * 37 + 1) +
  (30 * natBitLength p.primes.card + p.primes.card * (30 * B + 39) + 37) +
  (30 * ((parameterTailScalars p).map natBitLength).sum + 34 * 9 + 1) +
  (30 * natBitLength p.factors.length + p.factors.length * (30 * B + 39) + 37) + 3

/-- `sec:params`, paper/paper.tex: the retained
scalar list contains every scalar and rational component exactly once. -/
theorem parameterScalars_length (p : Cells.Parameters) : (parameterScalars p).length = 46 := by
  simp [parameterScalars, parameterHeadScalars_length, parameterTailScalars_length]

end NearQuarticWires.StageLift
