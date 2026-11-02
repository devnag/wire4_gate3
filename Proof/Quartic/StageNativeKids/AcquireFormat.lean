import Proof.Quartic.StageNativeKids.AcquiredWord
import Proof.Quartic.StageNativeKids.MarkedCopy

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
actual retained original source and real role-callee reply supply the
next cold source record, with exactly five trailing empty fields. -/
def acquireFormatProgram (P : Fin 3 ↪ Fin (ns + 1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (appendMarkedRecordsReset (P 0) (P 2) OP SC)
    (.seq (appendMarkedFrameReset (P 1) (P 2) OP SC)
      (.seq (emitWordM (P 2) OP (List.replicate 5 false)) (emitC (P 2) OP false)))

/-- `prop:time`, paper/paper.tex: the
acquired-source formatter pays both actual finite copies, all new
markers, every empty-field delimiter and the final outer delimiter. -/
def acquireFormatCost (r : NativeKidsRequest) : ℕ :=
  100 * ((r.prefixFields.flatMap frame).length + 1) +
    100 * ((frame r.rolePayload).length + 1) + 200

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual source formatter constructs
the exact acquired eleven-field word, preserving both input streams. -/
theorem acquireFormatProgram_spec (cap : ℕ) (P : Fin 3 ↪ Fin (ns + 1))
    (OP SC : Fin nr) (hOS : OP ≠ SC) (r : NativeKidsRequest) (σ : WState ns nr)
    (hsrc : σ.st (P 0) = r.word) (hrole : σ.st (P 1) = frame r.rolePayload)
    (hh : ∀ i : Fin 3, σ.sh (P i) = 0) (hd : σ.st (P 2) = [])
    (hOP : σ.val OP = 0) (hSC : σ.val SC = 0)
    (hcap : 2 * (r.prefixFields.flatMap frame).length +
      2 * (frame r.rolePayload).length + 30 ≤ cap) :
    WExec cap (acquireFormatProgram P OP SC) σ
      (appendO σ (P 2) OP (frame r.acquiredWord)) (acquireFormatCost r) := by
  have hp {i j : Fin 3} : P i = P j ↔ i = j := P.injective.eq_iff
  have e1 := appendMarkedRecordsReset_spec cap (P 0) (P 2) OP SC
    (P.injective.ne (by decide)) hOS r.prefixFields (List.replicate 6 false)
    (prefixFields_nonempty r) rfl σ (by rw [hsrc, source_prefix]) (hh 0)
    (by rw [hh 2, hd]; rfl) hSC (by rw [hOP]; omega)
  let s1 := appendO σ (P 2) OP (marks (r.prefixFields.flatMap frame))
  have e2 := appendMarkedFrameReset_spec cap (P 1) (P 2) OP SC
    (P.injective.ne (by decide)) hOS r.rolePayload [] s1
    (by simp [s1, appendO, hp, hrole]) (by simp [s1, appendO, hp, hh])
    (by simp [s1, appendO, hh, hd]) (by simp [s1, appendO, hOS.symm, hSC])
    (by simp only [s1, appendO_val, Function.update_self, hOP, Nat.zero_add,
      Codec.marks_length]; omega)
  let s2 := appendO s1 (P 2) OP (marks (frame r.rolePayload))
  have e3 := emitWordM_spec cap (P 2) OP (List.replicate 5 false) s2
    (by simp [s2, s1, appendO, hh, hd, List.length_append])
    (by simp only [s2, s1, appendO_val, Function.update_self, hOP, Nat.zero_add,
      Codec.marks_length, List.length_replicate]; omega)
  let s3 := appendO s2 (P 2) OP (marks (List.replicate 5 false))
  have e4 := Codec.emitBit_spec cap (P 2) OP false s3
    (by simp [s3, s2, s1, appendO, hh, hd, List.length_append, Nat.add_assoc])
    (by simp only [s3, s2, s1, appendO_val, Function.update_self, hOP, Nat.zero_add,
      Codec.marks_length, List.length_replicate]; omega)
  refine (e1.seq (e2.seq (e3.seq e4))).cast cap ?_ (by
    unfold acquireFormatCost
    simp only [List.length_replicate]
    omega)
  simp only [s3, s2, s1, appendO_append, acquiredWord_frame, List.append_assoc]

end NearQuarticWires.StageNativeKids
