import Proof.Gates.Dispatch.Run
import Proof.Gates.Codec.PairFrame

/-!
# Framed output from binary arithmetic programs

Paper: `prop:time`, paper/paper.tex. Replacing each emitted
bit by its marked pair and adding the final zero produces an exact frame.
The transformation preserves the computation and increases its step count
by at most a factor of three, plus two final steps.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch

variable {V : ℕ} {C : Ctx}

def markedState (a : DS V) : DS V := { a with out := Streaming.marks a.out }

def markedOp : Op V → St V
  | .emit b => .seq (.op (.emit true)) (.op (.emit b))
  | o => .op o

def markedProgram : St V → St V
  | .op o => markedOp o
  | .seq s t => .seq (markedProgram s) (markedProgram t)
  | .ite c s t => .ite c (markedProgram s) (markedProgram t)
  | .loop c s => .loop c (markedProgram s)

theorem markedOp_spec {o : Op V} {a b : DS V} (h : OpEx C o a b) :
    Ex C (markedOp o) (markedState a) (markedState b) 3 := by
  cases h with
  | zero x a => exact Ex.mono (Ex.op (OpEx.zero x (markedState a))) (by omega)
  | inc x a hv => exact Ex.mono (Ex.op (OpEx.inc x (markedState a) hv)) (by omega)
  | add x y a hxy hv => exact Ex.mono (Ex.op (OpEx.add x y (markedState a) hxy hv)) (by omega)
  | sub x y a hxy hv => exact Ex.mono (Ex.op (OpEx.sub x y (markedState a) hxy hv)) (by omega)
  | copy x y a hxy => exact Ex.mono (Ex.op (OpEx.copy x y (markedState a) hxy)) (by omega)
  | half x a => exact Ex.mono (Ex.op (OpEx.half x (markedState a))) (by omega)
  | shl x a hv => exact Ex.mono (Ex.op (OpEx.shl x (markedState a) hv)) (by omega)
  | mul x y z a hxy hxz hyz hv =>
    exact Ex.mono (Ex.op (OpEx.mul x y z (markedState a) hxy hxz hyz hv)) (by omega)
  | dm x y q r a hxy hxq hxr hyq hyr hqr hy hv =>
    exact Ex.mono (Ex.op (OpEx.dm x y q r (markedState a) hxy hxq hxr hyq hyr hqr hy hv)) (by omega)
  | rdC x a hc => exact Ex.mono (Ex.op (OpEx.rdC x (markedState a) hc)) (by omega)
  | rstC a => exact Ex.mono (Ex.op (OpEx.rstC (markedState a))) (by omega)
  | rdW x a => exact Ex.mono (Ex.op (OpEx.rdW x (markedState a))) (by omega)
  | emit bit a =>
    have h1 := Ex.op (OpEx.emit true (markedState a)) (C := C)
    have h2 := Ex.op (OpEx.emit bit {markedState a with out := (markedState a).out ++ [true]}) (C := C)
    simpa [markedOp, markedState, Streaming.marks_append, Streaming.marks, List.append_assoc]
      using Ex.seq h1 h2

theorem markedCnd (c : Cnd V) (a : DS V) : c.eval (markedState a) = c.eval a := by
  cases c <;> rfl

theorem markedProgram_spec {s : St V} {a b : DS V} {n : ℕ} (h : Ex C s a b n) :
    Ex C (markedProgram s) (markedState a) (markedState b) (3 * n) := by
  induction h with
  | op h => exact markedOp_spec h
  | seq _ _ ih1 ih2 => exact Ex.mono (Ex.seq ih1 ih2) (by omega)
  | iteT hc he _ ih => exact Ex.mono (Ex.iteT hc (by rw [markedCnd]; exact he) ih) (by omega)
  | iteF hc he _ ih => exact Ex.mono (Ex.iteF hc (by rw [markedCnd]; exact he) ih) (by omega)
  | loopF hc he => exact Ex.mono (Ex.loopF hc (by rw [markedCnd]; exact he)) (by omega)
  | loopT hc he _ _ ih1 ih2 =>
    exact Ex.mono (Ex.loopT hc (by rw [markedCnd]; exact he) ih1 ih2) (by omega)
  | mono _ hn ih => exact Ex.mono ih (by omega)

def framedProgram (s : St V) : St V := .seq (markedProgram s) (.op (.emit false))

theorem framedProgram_spec {s : St V} {b : DS V} {n : ℕ}
    (h : Ex C s a0 b n) :
    Ex C (framedProgram s) a0 { b with out := frame b.out } (3 * n + 2) := by
  have h1 := markedProgram_spec h
  have h2 := Ex.op (OpEx.emit false (markedState b)) (C := C)
  simpa [framedProgram, markedState, a0, NearCubicGates.Close.Codec.frame_eq_marks,
    Streaming.marks, Nat.add_assoc] using Ex.seq h1 h2

end NearQuarticWires.StageOutput
