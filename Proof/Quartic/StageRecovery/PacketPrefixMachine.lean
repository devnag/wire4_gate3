import Proof.Quartic.StageRecovery.PacketPrefix
import Proof.Quartic.StageRecovery.PacketCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the original
native packet hint also bounds the actual requested prefix-count codec. -/
theorem PacketPrefixRequest.count_bits (r : PacketPrefixRequest) :
    natBitLength r.count ≤ natBitLength r.native.values.length := by
  apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by unfold natBitLength; omega)
  exact r.count_le.trans_lt (lt_natBitLength _)

/-- `prop:time`, paper/paper.tex: the existing
decoder's exact source clock uses the actual requested prefix count and
still pays its original physical native width and header fields. -/
def PacketPrefixRequest.steps (r : PacketPrefixRequest) : ℕ :=
  5 + ((30 * natBitLength r.native.hint + 30 * natBitLength r.native.modulus +
    30 * natBitLength r.count + 98) +
      ((40 * natBitLength r.count + 42) +
        (r.count * (200 * (r.native.hint + 1) + 4) + 4) + 1) + 1) + 1

/-- `prop:time`, paper/paper.tex: the actual prefix
packet word keeps the original small native hint as its leading field. -/
theorem PacketPrefixRequest.leading_hint (r : PacketPrefixRequest) :
    leadOnes r.word = natBitLength r.native.hint := by
  unfold PacketPrefixRequest.word
  simpa only [List.append_assoc] using
    NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.native.hint
      (natWord r.native.modulus ++ natWord r.count ++ packetStream r.native.width r.native.values)

/-- `prop:time`, paper/paper.tex: the real leading
hint supplies the same bounded binary workspace for prefix decoding. -/
theorem PacketPrefixRequest.context_width (r : PacketPrefixRequest) :
    64 * (r.native.hint + 1) ≤ (ctxOf packetCallee packetSizes r.word).Wd := by
  change 64 * (r.native.hint + 1) ≤ 2 ^ (1 * leadOnes r.word) * 64
  rw [r.leading_hint, Nat.one_mul]
  have h := lt_natBitLength r.native.hint
  omega

/-- `lem:print`, paper/paper.tex: the unchanged
packet decoder emits precisely the original-column prefix from the
complete actual padded native packet. No trailing-record length is observed. -/
theorem packetProgram_prefix_spec (C : Ctx) (r : PacketPrefixRequest)
    (hin : C.inp = r.word) (hwidth : 64 * (r.native.hint + 1) ≤ C.Wd) :
    Hs C packetProgram (a0 : DS VV MM) r.steps (fun b => b.out = r.output) := by
  have hqbits : natBitLength r.native.modulus ≤ r.native.hint := by unfold PacketRequest.hint; omega
  have hnbits : natBitLength r.count ≤ r.native.hint := by
    have h := r.count_bits
    unfold PacketRequest.hint
    omega
  have hwb : r.native.width ≤ r.native.hint := by unfold PacketRequest.hint; omega
  have hhb : natBitLength r.native.hint ≤ r.native.hint + 1 := nbl_le_self _
  have h8 : 8 ≤ r.native.hint := by unfold PacketRequest.hint; omega
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hqpow := lt_natBitLength r.native.modulus
  have h2q : 2 * r.native.modulus ≤ 2 ^ C.Wd := by
    have hle : 2 ^ (natBitLength r.native.modulus + 1) ≤ 2 ^ C.Wd :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hle
    omega
  have hnfit : r.count < 2 ^ C.Wd :=
    (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hsfit (v : ℕ) : natBitLength (naturalSign r.native.modulus v) + 2 < 2 ^ C.Wd := by
    rw [naturalSign_bits]
    omega
  have hmfit (v : ℕ) : natBitLength (naturalMagnitude r.native.modulus v) + 2 < 2 ^ C.Wd := by
    have h := r.native.magnitude_bits v
    omega
  unfold packetProgram PacketPrefixRequest.steps
  refine Hs.seq (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
    fun a ⟨hc, _, _, hip, hout, _, _, _, _⟩ => ?_
  have haf : C.inp.drop a.ip = natWord r.native.hint ++ natWord r.native.modulus ++
      natWord r.count ++ packetStream r.native.width r.native.values := by
    rw [hip]
    simpa only [a0, List.drop_zero, PacketPrefixRequest.word] using hin
  refine Hs.seq (packetFields_spec C a hc r.native.hint r.native.modulus r.count _ haf
    (by omega) (by omega) (by omega)) fun b ⟨_, hbq, hbn, hbi, hbo, hbc⟩ => ?_
  have ee := emitVariable_spec C b hbc countVar (by decide) (by omega) (by rw [hbn]; omega)
  rw [hbn] at ee
  refine Hs.seq ee fun d ⟨hdo, hdr, hdc, hdf⟩ => ?_
  have hdi : d.ip = b.ip := congrArg Prod.fst hdr
  have hdq : d.env modulusVar = r.native.modulus := by rw [hdf _ (by decide), hbq]
  have hdn : d.env countVar = r.count := by rw [hdf _ (by decide), hbn]
  have hinput : C.inp.drop d.ip = packetStream r.native.width r.native.values := by
    rw [hdi, hbi, hip]
    simp only [a0, Nat.zero_add]
    rw [hin]
    change ((natWord r.native.hint ++ natWord r.native.modulus ++ natWord r.count) ++
      packetStream r.native.width r.native.values).drop _ = _
    exact List.drop_left
  refine (packetList_prefix_spec C d hdc r.native.width r.native.modulus r.native.values r.count
    (200 * (r.native.hint + 1)) r.count_le hinput hdn hnfit r.native.values_fit
    (by omega) r.native.modulus_pos hdq h2q (by omega)
    (fun v _ => hsfit v) (fun v _ => hmfit v) (fun v _ => r.native.entry_cost v)).mono le_rfl ?_
  rintro e ⟨heo, _, _⟩
  rw [heo, hdo, hbo, hout]
  simp only [a0, List.nil_append, PacketPrefixRequest.output, listWord, List.length_map,
    List.flatMap_map, Function.comp_def, List.length_take, min_eq_left r.count_le]

/-- `prop:time`, paper/paper.tex: physical prefix
decoding pays the unchanged complete input and every actual source and
cleanup step through the existing ordinary binary compiler. -/
noncomputable def PacketPrefixRequest.budget (r : PacketPrefixRequest) : ℕ :=
  langBudget packetCallee packetSizes VV MM r.word r.steps

/-- `lem:print`, paper/paper.tex: the original actual
packet decoder uniformly emits the canonical requested prefix, retaining
native padded input only as part of its paid physical cleanup. -/
noncomputable def packetPrefixWordFunction :
    WordFunction PacketPrefixRequest PacketPrefixRequest.word PacketPrefixRequest.output
      PacketPrefixRequest.budget :=
  wordFunction_of_lang PacketPrefixRequest.word PacketPrefixRequest.output packetCallee packetSizes
    packetProgram PacketPrefixRequest.steps (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := packetProgram_prefix_spec
        (ctxOf packetCallee packetSizes r.word) r rfl r.context_width
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      have h := r.context_width
      change 1 ≤ (ctxOf packetCallee packetSizes r.word).Wd
      omega)

end NearQuarticWires.StageRecovery
