import Proof.Quartic.StageRecovery.PacketRequest
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WorkerArith.WorkerBounds (nbl_le_self)

/-- `lem:print`, paper/paper.tex: one fixed program
decodes the literal header and sequentially centers every native record. -/
def packetProgram : St VV MM :=
  .seq initP (.seq packetFields (.seq (emitVariable countVar) packetList))

/-- `prop:time`, paper/paper.tex: the exact charged
source-program budget includes initialization, header, count output,
and every native-record decoding operation. -/
def PacketRequest.steps (r : PacketRequest) : ℕ :=
  5 + ((30 * natBitLength r.hint + 30 * natBitLength r.modulus +
    30 * natBitLength r.values.length + 98) +
      ((40 * natBitLength r.values.length + 42) +
        (r.values.length * (200 * (r.hint + 1) + 4) + 4) + 1) + 1) + 1

/-- `lem:print`, paper/paper.tex: the cold native packet
program prints precisely the complete centered integer list. Its width
depends on binary dimensions rather than the number of table entries. -/
theorem packetProgram_spec (C : Ctx) (r : PacketRequest)
    (hin : C.inp = r.word) (hwidth : 64 * (r.hint + 1) ≤ C.Wd) :
    Hs C packetProgram (a0 : DS VV MM) r.steps (fun b => b.out = r.output) := by
  have hqbits : natBitLength r.modulus ≤ r.hint := by unfold PacketRequest.hint; omega
  have hnbits : natBitLength r.values.length ≤ r.hint := by unfold PacketRequest.hint; omega
  have hwb : r.width ≤ r.hint := by unfold PacketRequest.hint; omega
  have hhb : natBitLength r.hint ≤ r.hint + 1 :=
    NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self _
  have h8 : 8 ≤ r.hint := by unfold PacketRequest.hint; omega
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hqpow : r.modulus < 2 ^ natBitLength r.modulus := lt_natBitLength _
  have h2q : 2 * r.modulus ≤ 2 ^ C.Wd := by
    have hle : 2 ^ (natBitLength r.modulus + 1) ≤ 2 ^ C.Wd :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hle
    omega
  have hnfit : r.values.length < 2 ^ C.Wd :=
    (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hsfit (value : ℕ) : natBitLength (naturalSign r.modulus value) + 2 < 2 ^ C.Wd := by
    rw [naturalSign_bits]
    omega
  have hmfit (value : ℕ) : natBitLength (naturalMagnitude r.modulus value) + 2 < 2 ^ C.Wd := by
    have := r.magnitude_bits value
    omega
  unfold packetProgram PacketRequest.steps
  refine Hs.seq (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
    fun a ⟨hc, _, _, hip, hout, _, _, _, _⟩ => ?_
  have haf : C.inp.drop a.ip =
      natWord r.hint ++ natWord r.modulus ++ natWord r.values.length ++ packetStream r.width r.values := by
    rw [hip]
    simpa only [a0, List.drop_zero, PacketRequest.word] using hin
  refine Hs.seq (packetFields_spec C a hc r.hint r.modulus r.values.length _ haf
    (by omega) (by omega) (by omega)) fun b ⟨_, hbq, hbn, hbi, hbo, hbc⟩ => ?_
  have ee := emitVariable_spec C b hbc countVar (by decide) (by omega)
    (by rw [hbn]; omega)
  rw [hbn] at ee
  refine Hs.seq ee fun d ⟨hdo, hdr, hdc, hdf⟩ => ?_
  have hdi : d.ip = b.ip := congrArg Prod.fst hdr
  have hdq : d.env modulusVar = r.modulus := by rw [hdf _ (by decide), hbq]
  have hdn : d.env countVar = r.values.length := by rw [hdf _ (by decide), hbn]
  have hinput : C.inp.drop d.ip = packetStream r.width r.values := by
    rw [hdi, hbi, hip]
    simp only [a0, Nat.zero_add]
    rw [hin]
    change ((natWord r.hint ++ natWord r.modulus ++ natWord r.values.length) ++
      packetStream r.width r.values).drop _ = _
    exact List.drop_left
  refine (packetList_spec C d hdc r.width r.modulus r.values (200 * (r.hint + 1))
    hinput hdn hnfit r.values_fit (by omega) r.modulus_pos hdq h2q (by omega)
    (fun value _ => hsfit value) (fun value _ => hmfit value)
    (fun value _ => r.entry_cost value)).mono le_rfl ?_
  rintro e ⟨heo, _, _⟩
  rw [heo, hdo, hbo, hout]
  simp only [a0, List.nil_append]
  simp only [PacketRequest.output, listWord, List.length_map, List.flatMap_map,
    Function.comp_def]

end NearQuarticWires.StageRecovery
