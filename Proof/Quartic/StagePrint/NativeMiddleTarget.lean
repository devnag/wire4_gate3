import Proof.Quartic.StagePrint.CarrierEnvelopeTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.NativeMiddle
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- `lem:print`, paper/paper.tex: two actual
metadata fields surround one framed source field, with the unchanged
eleven-field native recovery record layout. -/
def word (modulus : ℕ) (payload : List Bool) (targetCount : ℕ) : List Bool :=
  Top.loadRec (natWord modulus) (frame payload) (natWord targetCount) [] [] [] [] [] [] [] []

/-- `lem:print` and `prop:time`, paper/paper.tex: a real framed-output computation replaces only the
middle payload. Both metadata fields are copied as their actual finite
bytes and the call, output copies and final resets are charged linearly. -/
structure Mapper {Request : Type} {input output : Request→List Bool} {calleeBudget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (output r)) calleeBudget)
    (modulus targetCount : Request→ℕ) where
  budget : Request→ℕ
  machine : WordFunction Request
    (fun r=>word (modulus r) (input r) (targetCount r))
    (fun r=>frame (word (modulus r) (output r) (targetCount r))) budget
  linear_budget : ∃ K : ℕ,∀ r,
    budget r≤K*((word (modulus r) (input r) (targetCount r)).length+calleeBudget r+1)

end NearQuarticWires.StagePrint.NativeMiddle
