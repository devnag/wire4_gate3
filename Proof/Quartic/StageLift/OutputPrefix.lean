import Proof.Quartic.StageRecovery.OutputFrame

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: prior serialized
fields remain an untouched output front during a subsequent source program. -/
def prefixOutput {V M : ℕ} (front : List Bool) (a : DS V M) : DS V M :=
  { a with out := front ++ a.out }

/-- `lem:print`, paper/paper.tex: a real instruction
has the same clock when it appends after an already emitted front. -/
theorem operation_prefixOutput {V M : ℕ} {C : Ctx} {o : Op V M}
    {a b : DS V M} {n : ℕ} (h : OpEx C o a b n) (front : List Bool) :
    OpEx C o (prefixOutput front a) (prefixOutput front b) n := by
  cases h <;>
    simp only [prefixOutput, DS.set, DS.adv, DS.rew, DS.put, DS.srt, DS.called,
      ← List.append_assoc] <;>
    constructor <;> assumption

/-- `lem:print`, paper/paper.tex: appending a
later physical source preserves all previously emitted bytes and adds
no input scan, output copy, or head rewind to its actual execution. -/
theorem execution_prefixOutput {V M : ℕ} {C : Ctx} {s : St V M}
    {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (front : List Bool) :
    Ex C s (prefixOutput front a) (prefixOutput front b) n := by
  induction h with
  | op h => exact Ex.op (operation_prefixOutput h front)
  | seq _ _ ih₁ ih₂ => exact Ex.seq ih₁ ih₂
  | iteT hc he _ ih => exact Ex.iteT hc he ih
  | iteF hc he _ ih => exact Ex.iteF hc he ih
  | loopF hc he => exact Ex.loopF hc he
  | loopT hc he _ _ ih₁ ih₂ => exact Ex.loopT hc he ih₁ ih₂
  | mono _ hnm ih => exact Ex.mono ih hnm

/-- `lem:print`, paper/paper.tex: the existing
literal framing transformation can follow unmarked index headers.
Every new payload bit and its delimiter is physically emitted and paid. -/
theorem framedProgram_afterPrefix {V M : ℕ} {C : Ctx} {s : St V M}
    {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (ha : a.out = []) (front : List Bool) :
    Ex C (StageRecovery.OutputFrame.framedProgram s) { a with out := front }
      { b with out := front ++ frame b.out } (3 * n + 2) := by
  have hf := execution_prefixOutput (StageRecovery.OutputFrame.framedProgram_spec h) front
  simpa only [prefixOutput, StageRecovery.OutputFrame.markedState,
    StageRecovery.OutputFrame.framedState, StageRecovery.OutputFrame.markedBits, ha,
    List.flatMap_nil, List.append_nil] using hf

end NearQuarticWires.StageLift
