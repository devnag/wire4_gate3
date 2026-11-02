import Proof.Quartic.StageLift.SourceLoopState
import Proof.Quartic.StageLift.OutputPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: retained source
metadata are independent of bytes already appended to output. -/
theorem CarrierStartData.withOutput {B1 B2 : ℕ} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} (ha : CarrierStartData r a) (output : List Bool) :
    CarrierStartData r { a with out := output } :=
  ⟨ha.originalCall, ha.scalarFields, ha.primeFields, ha.factorFields, ha.witnessBits,
    ha.gammaBits, ha.indexFields, ha.preparedBits, ha.preparedBytes, ha.degree, ha.arity,
    ha.exponent, ha.chains, ha.modulus, ha.prime, ha.signs, ha.kind, ha.walkIndex,
    ha.walkCount, ha.gammaCursor, ha.preparedCursor⟩

/-- `prop:time`, paper/paper.tex: output has no
arithmetic or callee-capacity reserve and cannot change source validity. -/
theorem source_valid_output {C : Ctx} {a : DS VV MM} (ha : Valid C a) (output : List Bool) :
    Valid C { a with out := output } :=
  ⟨ha.env_lt, ha.ip_le, ha.ram_lt, ha.rc_le, ha.kin_le, ha.kout_le, ha.kc_le⟩

/-- Step 3 and `lem:print`, paper/paper.tex: real all-walk source state is independent of the output
front used by the physical marker-emission transformation. -/
theorem WalkSourceState.withOutput {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {cursor : ℕ} {a : DS VV MM} (ha : WalkSourceState C r cursor a) (output : List Bool) :
    WalkSourceState C r cursor { a with out := output } :=
  ⟨ha.sources.withOutput output, ha.gammaCursor,
    ⟨ha.constants.z, ha.constants.one, ha.constants.two⟩,
    source_valid_output ha.validExceptCounter output, ha.inputEmpty⟩

end NearQuarticWires.StageLift
