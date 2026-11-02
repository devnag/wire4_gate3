import Proof.Quartic.StageRecovery.NativeHeaderBits
import Proof.Wire_3_5.PrimAsmWriteNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the eight binary-length
registers exclude both previously read modulus and native-width registers. -/
def nativeBitRegisters : Fin 8 ↪ Fin 10 where
  toFun := ![3, 0, 5, 6, 4, 8, 7, 9]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

/-- `lem:print`, paper/paper.tex: the literal native
width, modulus-codec length and full native census are read from actual
loaded streams; only the census is traversed as a numeric value. -/
def nativeDimensionsProgram : WMX 27 10 :=
  .seq (StagePrint.unaryRegister 16 0 1)
    (.seq (StagePrint.unaryRegister 2 0 2)
      (.seq (StagePrint.unaryRegister 18 0 3) (.wm (bitLenM nativeBitRegisters))))

/-- `prop:time`, paper/paper.tex: all unary scans and
the native-census bit-length loop have their literal source clocks. -/
def NativeRequest.dimensionsSteps (r : NativeRequest) : ℕ :=
  16 * r.table.q + 16 * natBitLength r.modulus + 76 * r.table.count + 105

/-- `lem:print`, paper/paper.tex: actual metadata
reads retain every encoded stream and leave their source heads at zero,
while placing exactly the real dimensions in four separate registers. -/
theorem nativeDimensionsProgram_spec (cap : ℕ) (r : NativeRequest) (σ : WState 27 10)
    (hQ : σ.st 16 = List.replicate r.table.q true)
    (hM : σ.st 2 = RepairRepresentation.natWord r.modulus)
    (hN : σ.st 18 = List.replicate r.table.count true)
    (hH : ∀ i, σ.sh i = 0) (hV : ∀ i, σ.val i = 0)
    (hcapQ : r.table.q + 1 ≤ cap) (hcapM : natBitLength r.modulus + 1 ≤ cap)
    (hcapN : r.table.count + 2 ≤ cap) :
    WXExec cap nativeDimensionsProgram σ
      ((((σ.setv 1 r.table.q).setv 2 (natBitLength r.modulus)).setv 3 r.table.count).setv 4
        (natBitLength r.table.count)) r.dimensionsSteps := by
  have eQ := StagePrint.unaryRegister_spec cap (16 : Fin 28) (0 : Fin 10) 1
    (by decide) σ r.table.q hQ (hH _) (hV _) (hV _) hcapQ
  let s1 := σ.setv 1 r.table.q
  have eM := natWordBitLength_spec cap (2 : Fin 28) (0 : Fin 10) 2
    (by decide) s1 r.modulus (by simpa [s1] using hM) (hH _)
    (by simp [s1, hV]) (by simp [s1, hV]) hcapM
  let s2 := s1.setv 2 (natBitLength r.modulus)
  have eN := StagePrint.unaryRegister_spec cap (18 : Fin 28) (0 : Fin 10) 3
    (by decide) s2 r.table.count (by simpa [s2, s1] using hN) (hH _)
    (by simp [s2, s1, hV]) (by simp [s2, s1, hV]) (by omega)
  let s3 := s2.setv 3 r.table.count
  have eB := bitLenM_spec cap nativeBitRegisters s3
    (by simp [s3, s2, s1, nativeBitRegisters, hV])
    (by simp [s3, s2, s1, nativeBitRegisters, hV])
    (by simp [s3, s2, s1, nativeBitRegisters, hV])
    (by simp [s3, s2, s1, nativeBitRegisters, hV])
    (by simp [s3, s2, s1, nativeBitRegisters, hV])
    (by simpa [s3, nativeBitRegisters] using hcapN)
  refine (eQ.seq (eM.seq (eN.seq (WXExec.wm eB)))).cast cap ?_ ?_
  · rfl
  · simp [NativeRequest.dimensionsSteps, s3, nativeBitRegisters]
    omega

end NearQuarticWires.StageRecovery
