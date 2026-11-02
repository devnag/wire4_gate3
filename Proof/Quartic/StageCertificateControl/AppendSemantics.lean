import Proof.Quartic.Program.Stages

/-!
# The certificate suffix of the retained preparation word

Paper: Step 2 of `sec:algorithm`, paper/paper.tex, and the witness convention.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicGates.Close.Interfaces
open NearCubicWires.RepairOrdinary

/-- Step 2 of `sec:algorithm`, paper/paper.tex,
appends one certificate frame on a dispatched call and no
additional payload on a closed or rejected call. -/
noncomputable def certificateSuffix (B1 B2 : ℕ) (c : Call) (w : List Bool) : List Bool :=
  match Program.dispatch B1 B2 c with
  | none => []
  | some p => frame (Program.certifiedBits (Program.runCall c p w))

/-- The exact output word of Step 2, `sec:algorithm`,
paper/paper.tex, preserves the whole original
preparation payload and appends only its certificate suffix. -/
theorem certWord_eq_prep_append (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    Program.certWord B1 B2 c w=Program.prepWord B1 B2 c w++certificateSuffix B1 B2 c w := by
  unfold Program.certWord Program.prepWord Program.stageWord certificateSuffix
  cases Program.dispatch B1 B2 c <;> simp only [List.append_nil,List.cons_append,List.append_assoc]

end NearQuarticWires.StageCertificateControl
