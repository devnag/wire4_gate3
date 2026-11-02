import Proof.Quartic.StageRecovery.NativeMetadata
import Proof.Wire_3_5.PrimAsmStarNums

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the actual decoder
hint includes native signed-record width and actual modulus/census bits. -/
def NativeRequest.nativeHint (r : NativeRequest) : ℕ :=
  r.table.q + natBitLength r.modulus + natBitLength r.table.count + 9

/-- `lem:print`, paper/paper.tex: the computed
integer is exactly the existing packet decoder's hint, with native
padding included in its complete census. -/
theorem NativeRequest.nativeHint_eq (r : NativeRequest) : r.nativeHint = r.packet.hint := by
  simp only [NativeRequest.nativeHint, NativeRequest.packet, PacketRequest.hint,
    tablePacket, tableNaturals_length]
  omega

/-- `lem:print`, paper/paper.tex: three physical
register additions and nine constant increments compute the unchanged
packet header hint from the actual dimension-read state. -/
def nativeHintProgram : WM 27 10 :=
  .seq (ParseNat.addTo 1 8 0)
    (.seq (ParseNat.addTo 2 8 0)
      (.seq (ParseNat.addTo 4 8 0) (StarNums.incN 8 9)))

/-- `prop:time`, paper/paper.tex: the hint uses
only linear work in the actual width and the two binary lengths. -/
def NativeRequest.hintSteps (r : NativeRequest) : ℕ :=
  18 * r.table.q + 18 * natBitLength r.modulus + 18 * natBitLength r.table.count + 48

/-- `lem:print`, paper/paper.tex: the actual
native hint computation changes only its destination register and
preserves every source byte and source head. -/
theorem nativeHintProgram_spec (cap : ℕ) (r : NativeRequest) (σ : WState 27 10)
    (hs : r.MetadataState σ) (hcap : r.nativeHint ≤ cap) :
    WExec cap nativeHintProgram σ (σ.setv 8 r.nativeHint) r.hintSteps := by
  obtain ⟨_, _, _, _, hv⟩ := hs
  have e1 := ParseNat.addTo_spec cap (1 : Fin 10) 8 0 (by decide) (by decide) (by decide)
    σ (by simp [hv]) (by simp [hv]; unfold NativeRequest.nativeHint at hcap; omega)
    (by simp [hv]; unfold NativeRequest.nativeHint at hcap; omega)
  let s1 := σ.setv 8 (σ.val 8 + σ.val 1)
  have e2 := ParseNat.addTo_spec cap (2 : Fin 10) 8 0 (by decide) (by decide) (by decide)
    s1 (by simp [s1, hv]) (by simp [s1, hv]; unfold NativeRequest.nativeHint at hcap; omega)
    (by simp [s1, hv]; unfold NativeRequest.nativeHint at hcap; omega)
  let s2 := s1.setv 8 (s1.val 8 + s1.val 2)
  have e3 := ParseNat.addTo_spec cap (4 : Fin 10) 8 0 (by decide) (by decide) (by decide)
    s2 (by simp [s2, s1, hv]) (by simp [s2, s1, hv]; unfold NativeRequest.nativeHint at hcap; omega)
    (by simp [s2, s1, hv]; unfold NativeRequest.nativeHint at hcap; omega)
  let s3 := s2.setv 8 (s2.val 8 + s2.val 4)
  have e4 := StarNums.incN_spec cap (8 : Fin 10) 9 s3
    (by simp [s3, s2, s1, hv]; exact hcap)
  refine (e1.seq (e2.seq (e3.seq e4))).cast cap ?_ ?_
  · simp [s3, s2, s1, hv, wsetv_setv, NativeRequest.nativeHint]
  · simp [s3, s2, s1, hv, NativeRequest.hintSteps]
    omega

end NearQuarticWires.StageRecovery
