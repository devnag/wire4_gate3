import Proof.Quartic.Machine.Interfaces
import Proof.Quartic.Cycle.ConditionalGamma

set_option autoImplicit false

namespace NearQuarticWires.Machine

open NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `cor:conditional`, paper/paper.tex: the cycle
request contains the generator parameters, prefix and closed walk. -/
structure GammaRequest where
  parameters : NearQuarticWires.Cycle.SeedParameters
  prefixLength : ℕ
  prefixCode : ℕ
  walk : NearQuarticWires.Cycle.Walk parameters.N 4
  prefixFits : prefixLength ≤ NearQuarticWires.Cycle.seedLength parameters
  prefixCodeFits : prefixCode < 2 ^ prefixLength

/-- `cor:conditional`, paper/paper.tex: all numeric seed and walk
fields are explicit input words; no conditional-expectation oracle is read. -/
def gammaRequestWord (request : GammaRequest) : List Bool :=
  NearCubicWires.RepairRepresentation.natWord request.parameters.ell ++
    NearCubicWires.RepairRepresentation.natWord request.parameters.kh ++
    NearCubicWires.RepairRepresentation.natWord request.parameters.Q ++
    NearCubicWires.RepairRepresentation.natWord request.prefixLength ++
    NearCubicWires.RepairRepresentation.natWord request.prefixCode ++
    listWord NearCubicWires.RepairRepresentation.natWord
      (List.ofFn fun slot => (request.walk slot).val)

/-- `cor:conditional`, paper/paper.tex: the signed INTEGER
numerator `2^S c_prefix(w)`, not a nonnegative count or a real oracle. -/
noncomputable def gammaTarget (request : GammaRequest) : ℤ :=
  NearQuarticWires.Cycle.scaledGamma request.parameters request.prefixLength
    request.prefixCode request.walk

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the machine obligation for the efficient realization,
discharged by `StageGamma.gammaProgramObligation`. The completion-sum definition of `gammaTarget` is the specification,
not the algorithm. -/
def GammaProgramObligation (budget : GammaRequest → ℕ) : Prop :=
  Nonempty (WordFunction GammaRequest gammaRequestWord
    (fun request => intWord (gammaTarget request)) budget)

end NearQuarticWires.Machine
