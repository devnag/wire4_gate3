import Proof.Quartic.StageRecovery.FamilyProgram

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab

/-- `prop:time`, paper/paper.tex: the family generator
charges the original setup, complete support recurrence, sequential
copy and closure, and all final physical tape-head returns. -/
def FamilyRequest.budget (r : FamilyRequest) : ℕ := 2 * r.steps + 2

/-- `lem:print`, paper/paper.tex: an actual cold-input
ordinary word function generates all degree-bounded Boolean support
records from finite setup fields; the input contains no support list. -/
noncomputable def familyWordFunction :
    WordFunction FamilyRequest FamilyRequest.word FamilyRequest.output FamilyRequest.budget :=
  wordFunction_of_ideal familyProgram 16 (by decide) FamilyRequest.capacity FamilyRequest.lens
    FamilyRequest.steps (fun _ => le_rfl) (fun r => ⟨by rfl, familyProgram_spec r⟩)

end NearQuarticWires.StageRecovery
