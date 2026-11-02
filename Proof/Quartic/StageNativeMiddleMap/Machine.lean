import Proof.Quartic.StageNativeMiddleMap.Execution

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `prop:time`, paper/paper.tex: the
actual compiled mapper pays its source execution and complete
physical head return, with one linear factor of the callee budget. -/
def mapperBudget (recordLength calleeBudget : ℕ) : ℕ :=
  2*sourceSteps recordLength calleeBudget+2

/-- `lem:print`, paper/paper.tex: this
is an actual cold word function on the unchanged eleven-field
record, with neither a decoded-field nor output-length premise. -/
noncomputable def middleWordFunction {Request : Type} {input output : Request→List Bool}
    {calleeBudget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (output r)) calleeBudget)
    (modulus targetCount : Request→ℕ) :
    WordFunction Request
      (fun r=>StagePrint.NativeMiddle.word (modulus r) (input r) (targetCount r))
      (fun r=>frame (StagePrint.NativeMiddle.word (modulus r) (output r) (targetCount r)))
      (fun r=>mapperBudget (StagePrint.NativeMiddle.word (modulus r) (input r) (targetCount r)).length
        (calleeBudget r)) :=
  wordFunction_of_ideal (program f.program) (final f.program)
    (by change f.program.tapeCount+19≠0;omega)
    (fun r=>sourceSteps (StagePrint.NativeMiddle.word (modulus r) (input r) (targetCount r)).length (calleeBudget r))
    (fun r=>lens f.program (sourceSteps
      (StagePrint.NativeMiddle.word (modulus r) (input r) (targetCount r)).length (calleeBudget r)))
    (fun r=>sourceSteps (StagePrint.NativeMiddle.word (modulus r) (input r) (targetCount r)).length (calleeBudget r))
    (fun _=>le_rfl)
    (by
      intro r
      exact ⟨by simp [lens,final],program_exec f r (modulus r) (targetCount r)⟩)

/-- `prop:time`, paper/paper.tex: the
same actual mapper clock is linear in actual source bytes and callee
steps, even for arbitrary-magnitude encoded metadata values. -/
theorem mapperBudget_linear (recordLength calleeBudget : ℕ) :
    mapperBudget recordLength calleeBudget ≤ 2000002*(recordLength+calleeBudget+1) := by
  unfold mapperBudget sourceSteps
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: a complete actual middle-field mapper,
including its own fixed ordinary machine and its same-budget linear
bound, is constructed from the actual framed-output callee alone. -/
noncomputable def middleMapper {Request : Type} {input output : Request→List Bool}
    {calleeBudget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (output r)) calleeBudget)
    (modulus targetCount : Request→ℕ) : StagePrint.NativeMiddle.Mapper f modulus targetCount where
  budget:=fun r=>mapperBudget
    (StagePrint.NativeMiddle.word (modulus r) (input r) (targetCount r)).length (calleeBudget r)
  machine:=middleWordFunction f modulus targetCount
  linear_budget:=⟨2000002,fun _=>mapperBudget_linear _ _⟩

end NearQuarticWires.StageNativeMiddleMap
