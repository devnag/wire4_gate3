import Proof.Quartic.StageCertTests.SignedRequest
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WorkerArith.WorkerBounds (nbl_le_self)
open StageRecovery (packetFields packetFields_spec emitVariable emitVariable_spec countVar)

/-- `lem:print`, paper/paper.tex:
one fixed program initializes its bank, reads the native header, and
emits the complete canonical signed list. -/
def signedProgram : St VV MM :=
  .seq initP (.seq packetFields (.seq (emitVariable countVar) signedList))

/-- `prop:time`, paper/paper.tex:
the source clock includes initialization, header, count output and
every signed native-record operation. -/
def SignedRequest.steps (r : SignedRequest) : ℕ :=
  5 + ((30 * natBitLength r.hint + 30 * natBitLength 0 +
    30 * natBitLength r.values.length + 98) +
      ((40 * natBitLength r.values.length + 42) +
        (r.values.length * (200 * (r.hint+1)+4)+4)+1)+1)+1

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: a cold physical program converts
the actual signed table stream without discarding negative moments. -/
theorem signedProgram_spec (C : Ctx) (r : SignedRequest)
    (hin : C.inp = r.word) (hwidth : 64 * (r.hint+1) ≤ C.Wd) :
    Hs C signedProgram (a0 : DS VV MM) r.steps (fun b => b.out = r.output) := by
  have hnbits : natBitLength r.values.length ≤ r.hint := by unfold SignedRequest.hint; omega
  have hwb : r.width ≤ r.hint := by unfold SignedRequest.hint; omega
  have hhb : natBitLength r.hint ≤ r.hint+1 :=
    NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self _
  have h8 : 8 ≤ r.hint := by unfold SignedRequest.hint; omega
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hnfit : r.values.length < 2 ^ C.Wd :=
    (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hsfit (z : ℤ) : natBitLength (if z < 0 then 1 else 0)+2 < 2 ^ C.Wd := by
    rw [signed_sign_bits]
    omega
  have hmfit (z : ℤ) (hz : z ∈ r.values) : natBitLength z.natAbs+2 < 2 ^ C.Wd := by
    have := r.magnitude_bits z hz
    omega
  unfold signedProgram SignedRequest.steps
  refine Hs.seq (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
    fun a ⟨hc,_,_,hip,hout,_,_,_,_⟩ => ?_
  have haf : C.inp.drop a.ip =
      natWord r.hint ++ natWord 0 ++ natWord r.values.length ++ signedStream r.width r.values := by
    rw [hip]
    simpa only [a0,List.drop_zero,SignedRequest.word] using hin
  refine Hs.seq (packetFields_spec C a hc r.hint 0 r.values.length _ haf
    (by omega) (by norm_num [natBitLength];omega) (by omega))
    fun b ⟨_,_,hbn,hbi,hbo,hbc⟩ => ?_
  have ee := emitVariable_spec C b hbc countVar (by decide) (by omega)
    (by rw [hbn];omega)
  rw [hbn] at ee
  refine Hs.seq ee fun d ⟨hdo,hdr,hdc,hdf⟩ => ?_
  have hdi : d.ip = b.ip := congrArg Prod.fst hdr
  have hdn : d.env countVar = r.values.length := by rw [hdf _ (by decide),hbn]
  have hinput : C.inp.drop d.ip = signedStream r.width r.values := by
    rw [hdi,hbi,hip]
    simp only [a0,Nat.zero_add]
    rw [hin]
    change ((natWord r.hint ++ natWord 0 ++ natWord r.values.length) ++
      signedStream r.width r.values).drop _ = _
    exact List.drop_left
  refine (signedList_spec C d hdc r.width r.values (200 * (r.hint+1))
    hinput hdn hnfit r.values_fit (by omega) (by omega)
    (fun z _ => hsfit z) hmfit r.entry_cost).mono le_rfl ?_
  rintro e ⟨heo,_,_⟩
  rw [heo,hdo,hbo,hout]
  simp only [a0,List.nil_append]
  rfl

end NearQuarticWires.StageCertTests
