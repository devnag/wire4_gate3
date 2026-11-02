import Proof.Gates.Cells.Lang
import Proof.Gates.Codec.PairFrame

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery.OutputFrame

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print` and `prop:time`, paper/paper.tex: one true marker precedes every actual emitted payload bit. -/
def markedBits (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

/-- `lem:print` and `prop:time`, paper/paper.tex: output marking changes only the output word of the complete machine state. -/
def markedState {V M : ℕ} (a : DS V M) : DS V M := { a with out := markedBits a.out }

/-- `lem:print` and `prop:time`, paper/paper.tex: each ordinary output instruction emits its marker and original bit. -/
def markedOperation {V M : ℕ} : Op V M → St V M
  | .emit b => .seq (.op (.emit true)) (.op (.emit b))
  | o => .op o

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal syntax transformation retains every other source operation and finite branch. -/
def markedProgram {V M : ℕ} : St V M → St V M
  | .op o => markedOperation o
  | .seq s t => .seq (markedProgram s) (markedProgram t)
  | .ite c s t => .ite c (markedProgram s) (markedProgram t)
  | .loop c s => .loop c (markedProgram s)

/-- `lem:print` and `prop:time`, paper/paper.tex: every charged primitive operation has its exact marked execution with at most a factor three in cost. -/
theorem markedOperation_spec {V M : ℕ} {C : Ctx} {o : Op V M} {a b : DS V M}
    {k : ℕ} (h : OpEx C o a b k) : Ex C (markedOperation o) (markedState a) (markedState b) (3 * k) := by
  cases h with
  | zero x a =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.zero x (markedState a))) (by decide : 1 ≤ 3))
  | inc x a h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.inc x (markedState a) h)) (by decide : 1 ≤ 3))
  | add x y a hxy h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.add x y (markedState a) hxy h)) (by decide : 1 ≤ 3))
  | sub x y a hxy h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.sub x y (markedState a) hxy h)) (by decide : 1 ≤ 3))
  | copy x y a hxy =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.copy x y (markedState a) hxy)) (by decide : 1 ≤ 3))
  | half x a =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.half x (markedState a))) (by decide : 1 ≤ 3))
  | shl x a h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.shl x (markedState a) h)) (by decide : 1 ≤ 3))
  | mul x y z a hxy hxz hyz h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.mul x y z (markedState a) hxy hxz hyz h)) (by decide : 1 ≤ 3))
  | dm x y q r a hxy hxq hxr hyq hyr hqr hy hb =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.dm x y q r (markedState a) hxy hxq hxr hyq hyr hqr hy hb))
        (by decide : 1 ≤ 3))
  | rdI x a h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.rdI x (markedState a) h)) (by decide : 1 ≤ 3))
  | bkI a h =>
    simpa [markedOperation, markedState] using
      (Ex.mono (Ex.op (OpEx.bkI (markedState a) h)) (by decide : 1 ≤ 3))
  | rdM m x a h =>
    simpa [markedOperation, markedState, DS.set, DS.adv] using
      (Ex.mono (Ex.op (OpEx.rdM m x (markedState a) h)) (by decide : 1 ≤ 3))
  | wrM m x a h =>
    simpa [markedOperation, markedState, DS.put] using
      (Ex.mono (Ex.op (OpEx.wrM m x (markedState a) h)) (by decide : 1 ≤ 3))
  | rwM m a =>
    simpa [markedOperation, markedState, DS.rew] using
      (Ex.mono (Ex.op (OpEx.rwM m (markedState a))) (by omega : a.rc m + 1 ≤ 3 * (a.rc m + 1)))
  | srtM m a h =>
    simpa [markedOperation, markedState, DS.srt] using
      (Ex.mono (Ex.op (OpEx.srtM m (markedState a) h))
        (by omega : (a.ram m).length + 1 ≤ 3 * ((a.ram m).length + 1)))
  | kem bit a h =>
    simpa [markedOperation, markedState] using
      (Ex.mono (Ex.op (OpEx.kem bit (markedState a) h)) (by decide : 1 ≤ 3))
  | kcall r a hi hb =>
    simpa [markedOperation, markedState, DS.called] using
      (Ex.mono (Ex.op (OpEx.kcall r (markedState a) hi hb))
        (by omega : 1 + C.Lk + C.Bk ≤ 3 * (1 + C.Lk + C.Bk)))
  | rdK x a h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.rdK x (markedState a) h)) (by decide : 1 ≤ 3))
  | emit bit a =>
    have hs := Ex.seq (C := C) (Ex.op (OpEx.emit true (markedState a)))
      (Ex.op (OpEx.emit bit { markedState a with out := (markedState a).out ++ [true] }))
    simpa [markedOperation, markedState, markedBits, List.flatMap_append,
      List.append_assoc] using hs

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete marked program preserves the original state transition and triples only its charged execution clock. -/
theorem markedProgram_spec {V M : ℕ} {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ}
    (h : Ex C s a b n) : Ex C (markedProgram s) (markedState a) (markedState b) (3 * n) := by
  induction h with
  | op h => exact markedOperation_spec h
  | seq _ _ ih1 ih2 => exact Ex.mono (Ex.seq ih1 ih2) (by omega)
  | iteT hc he _ ih => exact Ex.mono (Ex.iteT hc he ih) (by omega)
  | iteF hc he _ ih => exact Ex.mono (Ex.iteF hc he ih) (by omega)
  | loopF hc he => exact Ex.mono (Ex.loopF hc he) (by omega)
  | loopT hc he _ _ ih1 ih2 => exact Ex.mono (Ex.loopT hc he ih1 ih2) (by omega)
  | mono _ hnm ih => exact Ex.mono ih (Nat.mul_le_mul_left _ hnm)

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete output-framing program emits one final false delimiter. -/
def framedProgram {V M : ℕ} (s : St V M) : St V M :=
  .seq (markedProgram s) (.op (.emit false))

/-- `lem:print` and `prop:time`, paper/paper.tex: only the output word is replaced by its exact complete frame. -/
def framedState {V M : ℕ} (a : DS V M) : DS V M := { a with out := frame a.out }

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal framing program writes the exact complete frame in 3*n+2 source operations, retaining all other state components. -/
theorem framedProgram_spec {V M : ℕ} {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ}
    (h : Ex C s a b n) :
    Ex C (framedProgram s) (markedState a) (framedState b) (3 * n + 2) := by
  have hm := markedProgram_spec h
  have he := Ex.seq hm (Ex.op (OpEx.emit false (markedState b)))
  convert he using 1
  · rfl
  · rw [framedState, markedState, NearCubicGates.Close.Codec.frame_eq_marks]
    rfl

end NearQuarticWires.StageRecovery.OutputFrame
