import Proof.Quartic.StageRecovery.NativeHint
import Proof.Gates.Codec.Emit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

/-- `lem:print`, paper/paper.tex: the small hint
writer has six cleared scratch registers and a separate output position. -/
def nativeHeaderRegisters : Fin 8 ↪ Fin 10 where
  toFun := ![8, 0, 1, 2, 4, 5, 6, 9]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

/-- `lem:print`, paper/paper.tex: the literal
physical header output is the unchanged decoder hint and two actual
source codecs, with no native-table value included in the header. -/
def NativeRequest.header (r : NativeRequest) : List Bool :=
  RepairRepresentation.natWord r.packet.hint ++ RepairRepresentation.natWord r.modulus ++
    RepairRepresentation.natWord r.targetCount

/-- `lem:print`, paper/paper.tex: the three
metadata scratch registers are physically cleared before binary output. -/
def nativeHeaderClear : WM 27 10 :=
  .seq (WM.clear 1) (.seq (WM.clear 2) (WM.clear 4))

/-- `lem:print`, paper/paper.tex: the actual
header uses the existing small-number writer and literal codec-copy
passes, so no loop iterates through the modulus's numeric value. -/
def nativeHeaderEmitProgram : WM 27 10 :=
  .seq nativeHeaderClear
    (.seq (writeNatM 27 nativeHeaderRegisters)
      (.seq (Codec.copyNat false 2 27 nativeHeaderRegisters)
        (.seq (Codec.copyNat false 4 27 nativeHeaderRegisters) (emitC 27 9 false))))

/-- `prop:time`, paper/paper.tex: physical
header clearing, hint writing and both unchanged codec copies are charged. -/
def NativeRequest.headerEmitSteps (r : NativeRequest) : ℕ :=
  3 * r.table.q + 3 * natBitLength r.modulus + 3 * natBitLength r.table.count +
    (natBitLength r.packet.hint + 10) * (100 * r.packet.hint + 200) +
      60 * (RepairRepresentation.natWord r.modulus).length +
      60 * (RepairRepresentation.natWord r.targetCount).length + 140

/-- `lem:print`, paper/paper.tex: the cleared
writer state retains the actual hint and full native census, with every
other writer register zero and all source bytes unchanged. -/
theorem nativeHeaderClear_spec (cap : ℕ) (r : NativeRequest) (σ : WState 27 10)
    (hs : r.MetadataState σ) (hcap : r.nativeHint ≤ cap) :
    WExec cap nativeHeaderClear (σ.setv 8 r.nativeHint)
      ((((σ.setv 8 r.nativeHint).setv 1 0).setv 2 0).setv 4 0)
      (3 * r.table.q + 3 * natBitLength r.modulus + 3 * natBitLength r.table.count + 5) := by
  obtain ⟨_, _, _, _, hv⟩ := hs
  let a := σ.setv 8 r.nativeHint
  have e1 := wclear_spec cap (1 : Fin 10) r.table.q a (by simp [a, hv])
    (by simp [a, hv]; unfold NativeRequest.nativeHint at hcap; omega)
  let b := a.setv 1 0
  have e2 := wclear_spec cap (2 : Fin 10) (natBitLength r.modulus) b (by simp [b, a, hv])
    (by simp [b, a, hv]; unfold NativeRequest.nativeHint at hcap; omega)
  let c := b.setv 2 0
  have e3 := wclear_spec cap (4 : Fin 10) (natBitLength r.table.count) c (by simp [c, b, a, hv])
    (by simp [c, b, a, hv]; unfold NativeRequest.nativeHint at hcap; omega)
  exact (e1.seq (e2.seq e3)).cast cap rfl (by omega)

/-- `lem:print`, paper/paper.tex: the actual
metadata state is serialized into the complete framed existing decoder
header, by physical writing and source copying only. -/
theorem nativeHeaderEmitProgram_spec (cap : ℕ) (r : NativeRequest) (σ : WState 27 10)
    (hs : r.MetadataState σ)
    (hcap : r.packet.hint + 6 * natBitLength r.packet.hint + 2 * r.header.length + 20 ≤ cap) :
    Runs cap (.wm nativeHeaderEmitProgram) (σ.setv 8 r.nativeHint) r.headerEmitSteps
      (fun b => b.st 27 = frame r.header) := by
  obtain ⟨hM, hT, hO, hH, hv⟩ := hs
  have hhint : r.nativeHint ≤ cap := by rw [r.nativeHint_eq]; omega
  have eC := nativeHeaderClear_spec cap r σ ⟨hM, hT, hO, hH, hv⟩ hhint
  let c := (((σ.setv 8 r.nativeHint).setv 1 0).setv 2 0).setv 4 0
  have vc : c.val = ![0, 0, 0, r.table.count, 0, 0, 0, 0, r.packet.hint, 0] := by
    funext i
    fin_cases i <;> simp [c, hv, r.nativeHint_eq]
  have ew := writeNatM_spec cap (27 : Fin 28) nativeHeaderRegisters c
    (by simp [nativeHeaderRegisters, vc]) (by simp [nativeHeaderRegisters, vc])
    (by simp [nativeHeaderRegisters, vc]) (by simp [nativeHeaderRegisters, vc])
    (by simp [nativeHeaderRegisters, vc]) (by simp [nativeHeaderRegisters, vc])
    (by simpa [c, hH, hO, Nat.add_assoc])
    (by simp [nativeHeaderRegisters, vc]; omega)
  let a := appendO c 27 9 (marks (RepairRepresentation.natWord r.packet.hint))
  have ew' : WExec cap (writeNatM 27 nativeHeaderRegisters) c a
      ((natBitLength r.packet.hint + 10) * (100 * r.packet.hint + 200)) := by
    simpa [a, nativeHeaderRegisters, vc] using ew
  have eM := Codec.copyNat_spec cap false (2 : Fin 28) 27 (by decide)
    nativeHeaderRegisters r.modulus [] [] a
    (by simp [a, appendO, c, hM, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc]) (by simp [a, appendO, c, hH])
    (by simp [a, appendO, c, hH, hO, Nat.add_assoc])
    (by simp [a, appendO, nativeHeaderRegisters, vc])
    (by simp [a, appendO, nativeHeaderRegisters, vc])
    (by simp [a, appendO, nativeHeaderRegisters, vc, marks_length,
        NativeRequest.header, List.length_append] at *; omega)
  let b := (appendO a 27 9 (marks (RepairRepresentation.natWord r.modulus))).seth 2
    (RepairRepresentation.natWord r.modulus).length
  have eM' : WExec cap (Codec.copyNat false 2 27 nativeHeaderRegisters) a b
      (60 * (RepairRepresentation.natWord r.modulus).length + 60) := by
    simpa [b, nativeHeaderRegisters, stp] using eM
  have eT := Codec.copyNat_spec cap false (4 : Fin 28) 27 (by decide)
    nativeHeaderRegisters r.targetCount [] [] b
    (by simp [b, a, appendO, c, hT, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc]) (by simp [b, a, appendO, c, hH])
    (by simp [b, a, appendO, c, hH, hO, Nat.add_assoc])
    (by simp [b, a, appendO, nativeHeaderRegisters, vc])
    (by simp [b, a, appendO, nativeHeaderRegisters, vc])
    (by simp [b, a, appendO, nativeHeaderRegisters, vc, marks_length,
        NativeRequest.header, List.length_append] at *; omega)
  let d := (appendO b 27 9 (marks (RepairRepresentation.natWord r.targetCount))).seth 4
    (RepairRepresentation.natWord r.targetCount).length
  have eT' : WExec cap (Codec.copyNat false 4 27 nativeHeaderRegisters) b d
      (60 * (RepairRepresentation.natWord r.targetCount).length + 60) := by
    simpa [d, nativeHeaderRegisters, stp] using eT
  have eF := Codec.emitBit_spec cap (27 : Fin 28) (9 : Fin 10) false d
    (by simp [d, b, a, appendO, c, hH, hO, Nat.add_assoc])
    (by simp [d, b, a, appendO, vc, marks_length,
        NativeRequest.header, List.length_append] at *; omega)
  refine ⟨_, (WXExec.wm (eC.seq (ew'.seq (eM'.seq (eT'.seq eF))))).mono ?_, ?_⟩
  · unfold NativeRequest.headerEmitSteps
    omega
  · simp [d, b, a, appendO, c, hO, NativeRequest.header, Codec.frame_eq_marks,
      List.append_assoc, Streaming.marks_append]

end NearQuarticWires.StageRecovery
