import Proof.Quartic.StagePrintTuple.KernelLayout

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: a fixed sum
of the genuine callee tape counts supplies a constant reusable work
bank, independently of every source request or Terms count. -/
@[irreducible] noncomputable def termStageSpan (native : Program) : ℕ := kernelSpan native

private theorem sum_fits (a b c d e : ℕ) :
    a ≤ a+b+c+d+e ∧ b ≤ a+b+c+d+e ∧ c ≤ a+b+c+d+e ∧
      d ≤ a+b+c+d+e ∧ e ≤ a+b+c+d+e := by omega

/-- `lem:print`, paper/paper.tex: the actual
native source printer fits the fixed source work bank. -/
theorem termStageSpan_native (native : Program) : native.tapeCount ≤ termStageSpan native := by
  unfold termStageSpan kernelSpan
  exact (sum_fits _ _ _ _ _).1

/-- `lem:print`, paper/paper.tex: the actual
support selector fits the same fixed bank without a runtime allocator. -/
theorem termStageSpan_support (native : Program) :
    supportIndexWordFunction.program.tapeCount ≤ termStageSpan native := by
  unfold termStageSpan kernelSpan
  exact (sum_fits _ _ _ _ _).2.1

/-- `lem:print`, paper/paper.tex: the actual
signed-coefficient converter fits the same fixed bank. -/
theorem termStageSpan_coefficient (native : Program) :
    coefficientWordFunction.program.tapeCount ≤ termStageSpan native := by
  unfold termStageSpan kernelSpan
  exact (sum_fits _ _ _ _ _).2.2.1

/-- `lem:print`, paper/paper.tex: the actual
Cartesian tuple printer fits the same constant reusable bank. -/
theorem termStageSpan_tuple (native : Program) :
    tupleRecordPrinter.program.tapeCount ≤ termStageSpan native := by
  unfold termStageSpan kernelSpan
  exact (sum_fits _ _ _ _ _).2.2.2.1

/-- `lem:print`, paper/paper.tex: the actual
signed Stack printer fits the same constant reusable bank. -/
theorem termStageSpan_stack (native : Program) :
    stackRecordPrinter.program.tapeCount ≤ termStageSpan native := by
  unfold termStageSpan kernelSpan
  exact (sum_fits _ _ _ _ _).2.2.2.2

end NearQuarticWires.StageTuple
