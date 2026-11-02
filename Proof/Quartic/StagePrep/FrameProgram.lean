import Proof.Gates.Dispatch.Lang
import Proof.Gates.Codec.PairFrame

/-!
# Framing the parameter-preparation output

Paper: the encoded calls and outputs of `thm:counter`,
paper/paper.tex, and polynomial preparation in
`prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary

/-- The marked payload encoding for the words in
`sec:counting`, paper/paper.tex. -/
def markedBits (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

/-- The output-marked state for the preparation computation of
`prop:time`, paper/paper.tex. -/
def markedState {V : ℕ} (a : DS V) : DS V := { a with out := markedBits a.out }

/-- Emission lowering for the output encoding of `thm:counter`,
paper/paper.tex. -/
def markedOperation {V : ℕ} : Op V → St V
  | .emit b => .seq (.op (.emit true)) (.op (.emit b))
  | o => .op o

/-- The output-marking translation for the preparation program
in `prop:time`, paper/paper.tex. -/
def markedProgram {V : ℕ} : St V → St V
  | .op o => markedOperation o
  | .seq s t => .seq (markedProgram s) (markedProgram t)
  | .ite c s t => .ite c (markedProgram s) (markedProgram t)
  | .loop c s => .loop c (markedProgram s)

/-- One preparation operation of `prop:time`, paper/paper.tex, has an exact marked execution in at most three
language steps. -/
theorem markedOperation_spec {V : ℕ} {C : Ctx} {o : Op V} {a b : DS V}
    (h : OpEx C o a b) : Ex C (markedOperation o) (markedState a) (markedState b) 3 := by
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
  | rdC x a h =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.rdC x (markedState a) h)) (by decide : 1 ≤ 3))
  | rstC a =>
    simpa [markedOperation, markedState] using
      (Ex.mono (Ex.op (OpEx.rstC (markedState a))) (by decide : 1 ≤ 3))
  | rdW x a =>
    simpa [markedOperation, markedState, DS.set] using
      (Ex.mono (Ex.op (OpEx.rdW x (markedState a))) (by decide : 1 ≤ 3))
  | emit bit a =>
    have hs := Ex.seq (C := C) (Ex.op (OpEx.emit true (markedState a)))
      (Ex.op (OpEx.emit bit { markedState a with out := (markedState a).out ++ [true] }))
    simpa [markedOperation, markedState, markedBits, List.flatMap_append,
      List.append_assoc] using hs

/-- The preparation program of `prop:time`, paper/paper.tex, can mark every output bit with at most a factor
three in its full execution cost. -/
theorem markedProgram_spec {V : ℕ} {C : Ctx} {s : St V} {a b : DS V} {n : ℕ}
    (h : Ex C s a b n) : Ex C (markedProgram s) (markedState a) (markedState b) (3 * n) := by
  induction h with
  | op h => exact markedOperation_spec h
  | seq _ _ ih1 ih2 => exact Ex.mono (Ex.seq ih1 ih2) (by omega)
  | iteT hc he _ ih => exact Ex.mono (Ex.iteT hc he ih) (by omega)
  | iteF hc he _ ih => exact Ex.mono (Ex.iteF hc he ih) (by omega)
  | loopF hc he => exact Ex.mono (Ex.loopF hc he) (by omega)
  | loopT hc he _ _ ih1 ih2 => exact Ex.mono (Ex.loopT hc he ih1 ih2) (by omega)
  | mono _ hnm ih => exact Ex.mono ih (Nat.mul_le_mul_left _ hnm)

/-- The complete output frame of `thm:counter`, paper/paper.tex, adds its single terminal marker. -/
def framedProgram {V : ℕ} (s : St V) : St V :=
  .seq (markedProgram s) (.op (.emit false))

/-- The exact framed output state of `thm:counter`,
paper/paper.tex. -/
def framedState {V : ℕ} (a : DS V) : DS V := { a with out := frame a.out }

/-- The parameter-preparation output of `prop:time`,
paper/paper.tex, is framed by actual emitted bits
at a cost of `3*n+2`, preserving both input cursors. -/
theorem framedProgram_spec {V : ℕ} {C : Ctx} {s : St V} {a b : DS V} {n : ℕ}
    (h : Ex C s a b n) :
    Ex C (framedProgram s) (markedState a) (framedState b) (3 * n + 2) := by
  have hm := markedProgram_spec h
  have he := Ex.seq hm (Ex.op (OpEx.emit false (markedState b)))
  convert he using 1
  · rfl
  · rw [framedState, markedState, NearCubicGates.Close.Codec.frame_eq_marks]
    rfl

end NearQuarticWires.StagePrep
