import Proof.Wire_3_5.PrimAsmParseNat
import Proof.Gates.CounterAsm.Main
import Proof.Gates.Dispatch.ParamsF

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: only
the actual original bank size, original occurrence and original child
count are decoded into small loop registers; radix and walk stay binary. -/
def readSmallProgram (marked : Bool) (src : Fin (ns + 1))
    (R : Fin 5 ↪ Fin nr) : WM ns nr :=
  readNatM marked src (R 0) (R 1) (R 2) (R 3) (R 4)

/-- `prop:time`, paper/paper.tex: the
actual natural-codec reader has a quadratic clock in its small original
counter value, independent of every large binary context value. -/
theorem readSmall_clock (x : ℕ) :
    (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ 500 * (x + 1) ^ 2 := by
  have hb := NearCubicGates.Close.Dispatch.natBitLength_le_succ x
  have hp := NearCubicGates.Close.CounterAsm.two_pow_nbl_le x
  calc
    _ ≤ (x + 3) * (80 * (x + 1) + 40) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ _ := by nlinarith

/-- `lem:print` and `prop:time`, paper/paper.tex: the real small-counter reader consumes
its literal source codec, clears all four scratch registers, preserves
all other state, and pays the complete quadratic physical clock. -/
theorem readSmallProgram_spec (cap : ℕ) (marked : Bool) (src : Fin (ns + 1))
    (R : Fin 5 ↪ Fin nr) (x : ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src = pre ++ enc marked (natWord x) ++ rest)
    (hh : σ.sh src = pre.length) (hz : ∀ j, σ.val (R j) = 0)
    (hcap : 4 * (x + 1) ≤ cap) :
    WExec cap (readSmallProgram marked src R) σ
      ((σ.seth src (pre.length + stp marked * (natWord x).length)).setv (R 2) x)
      (500 * (x + 1) ^ 2) := by
  have hp := NearCubicGates.Close.CounterAsm.two_pow_nbl_le x
  have ep := readNatM_spec cap marked src (R 0) (R 1) (R 2) (R 3) (R 4)
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    x pre rest σ hs hh (hz 0) (hz 1) (hz 3) (hz 4)
    (by rw [hz 2, Nat.zero_add, pow_succ]; omega)
  simpa only [readSmallProgram, hz 2, Nat.zero_add] using ep.mono (readSmall_clock x)

end NearQuarticWires.StageNativeKids
