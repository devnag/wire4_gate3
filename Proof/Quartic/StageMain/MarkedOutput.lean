import Proof.Gates.Cells.Hs
import Proof.Foundations.OrdinaryMachine

/-!
# Physical framing of the main output

Step 4 of `sec:algorithm`, paper/paper.tex,
passes its exact record to Step 5. Replacing each output bit by its
marker and payload implements the required frame with at most three
times the original source-language clock; a final false bit closes it.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

variable {V M : ℕ}

def markOutputState (a : DS V M) : DS V M :=
  { a with out := a.out.flatMap (fun b => [true, b]) }

def markOutputProgram : St V M → St V M
  | .op (.emit b) => .seq (.op (.emit true)) (.op (.emit b))
  | .op o => .op o
  | .seq s t => .seq (markOutputProgram s) (markOutputProgram t)
  | .ite c s t => .ite c (markOutputProgram s) (markOutputProgram t)
  | .loop c s => .loop c (markOutputProgram s)

theorem markOutput_test (c : Cnd V) (a : DS V M) : c.eval (markOutputState a) = c.eval a := by
  cases c <;> rfl

theorem markOutput_op {C : Ctx} {o : Op V M} {a b : DS V M} {n : ℕ}
    (h : OpEx C o a b n) :
    Ex C (markOutputProgram (.op o)) (markOutputState a) (markOutputState b) (3 * n) := by
  cases h with
  | zero x a => exact (Ex.op (OpEx.zero x (markOutputState a))).mono (by omega)
  | inc x a hv => exact (Ex.op (OpEx.inc x (markOutputState a) hv)).mono (by omega)
  | add x y a hn hv => exact (Ex.op (OpEx.add x y (markOutputState a) hn hv)).mono (by omega)
  | sub x y a hn hv => exact (Ex.op (OpEx.sub x y (markOutputState a) hn hv)).mono (by omega)
  | copy x y a hn => exact (Ex.op (OpEx.copy x y (markOutputState a) hn)).mono (by omega)
  | half x a => exact (Ex.op (OpEx.half x (markOutputState a))).mono (by omega)
  | shl x a hv => exact (Ex.op (OpEx.shl x (markOutputState a) hv)).mono (by omega)
  | mul x y z a hxy hxz hyz hv => exact (Ex.op (OpEx.mul x y z (markOutputState a) hxy hxz hyz hv)).mono (by omega)
  | dm x y q r a hxy hxq hxr hyq hyr hqr hy hv =>
    exact (Ex.op (OpEx.dm x y q r (markOutputState a) hxy hxq hxr hyq hyr hqr hy hv)).mono (by omega)
  | rdI x a hp => exact (Ex.op (OpEx.rdI x (markOutputState a) hp)).mono (by omega)
  | bkI a hp => exact (Ex.op (OpEx.bkI (markOutputState a) hp)).mono (by omega)
  | emit bit a =>
    have he := Ex.seq (Ex.op (OpEx.emit (C := C) true (markOutputState a)))
      (Ex.op (OpEx.emit (C := C) bit { markOutputState a with out := (markOutputState a).out ++ [true] }))
    simpa [markOutputProgram, markOutputState, List.append_assoc] using he
  | rdM m x a hp => exact (Ex.op (OpEx.rdM m x (markOutputState a) hp)).mono (by omega)
  | wrM m x a hp => exact (Ex.op (OpEx.wrM m x (markOutputState a) hp)).mono (by omega)
  | rwM m a => exact (Ex.op (OpEx.rwM m (markOutputState a))).mono (by dsimp only [markOutputState]; omega)
  | srtM m a hp => exact (Ex.op (OpEx.srtM m (markOutputState a) hp)).mono (by dsimp only [markOutputState]; omega)
  | kem bit a hp => exact (Ex.op (OpEx.kem bit (markOutputState a) hp)).mono (by omega)
  | kcall r a hin hb => exact (Ex.op (OpEx.kcall r (markOutputState a) hin hb)).mono (by omega)
  | rdK x a hp => exact (Ex.op (OpEx.rdK x (markOutputState a) hp)).mono (by omega)

theorem markOutput_run {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ}
    (h : Ex C s a b n) :
    Ex C (markOutputProgram s) (markOutputState a) (markOutputState b) (3 * n) := by
  induction h with
  | op h => exact markOutput_op h
  | seq _ _ ih1 ih2 => exact (Ex.seq ih1 ih2).mono (by omega)
  | iteT hc he _ ih =>
    exact (Ex.iteT hc (by rw [markOutput_test]; exact he) ih).mono (by omega)
  | iteF hc he _ ih =>
    exact (Ex.iteF hc (by rw [markOutput_test]; exact he) ih).mono (by omega)
  | loopF hc he => exact (Ex.loopF hc (by rw [markOutput_test]; exact he)).mono (by omega)
  | loopT hc he _ _ ih1 ih2 =>
    exact (Ex.loopT hc (by rw [markOutput_test]; exact he) ih1 ih2).mono (by omega)
  | mono _ hnm ih => exact ih.mono (by omega)

def framedOutputProgram (s : St V M) : St V M :=
  .seq (markOutputProgram s) (.op (.emit false))

theorem framedOutput_run {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ}
    (h : Ex C s a b n) :
    Ex C (framedOutputProgram s) (markOutputState a) { b with out := frame b.out } (3 * n + 2) := by
  have he := Ex.seq (markOutput_run h) (Ex.op (OpEx.emit (C := C) false (markOutputState b)))
  have hframe : b.out.flatMap (fun bit => [true, bit]) ++ [false] = frame b.out := by
    induction b.out with
    | nil => rfl
    | cons bit bits ih => simpa [frame, List.append_assoc] using congrArg (fun xs => true :: bit :: xs) ih
  simpa only [framedOutputProgram, markOutputState, hframe, Nat.add_assoc] using he

end NearQuarticWires.StageMain
