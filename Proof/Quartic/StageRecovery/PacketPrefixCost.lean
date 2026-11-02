import Proof.Quartic.StageRecovery.PacketPrefixMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: replacing the
native count field by a bounded target-prefix count does not increase
the actual encoded input length; the whole native record stream remains. -/
theorem PacketPrefixRequest.word_length_le (r : PacketPrefixRequest) :
    r.word.length ≤ r.native.word.length := by
  have hb := r.count_bits
  simp only [PacketPrefixRequest.word, PacketRequest.word, List.length_append,
    NearCubicGates.Close.Cells.natWord_length]
  omega

/-- `prop:time`, paper/paper.tex: the same physical
decoder performs no more source operations on the target prefix than
on the complete native count, including its literal count codec. -/
theorem PacketPrefixRequest.steps_le (r : PacketPrefixRequest) :
    r.steps ≤ r.native.steps := by
  have hb := r.count_bits
  have hn := r.count_le
  unfold PacketPrefixRequest.steps PacketRequest.steps
  gcongr

/-- `prop:time`, paper/paper.tex: prefix recovery
retains the original small workspace hint and pays at most the original
complete-packet budget, including all trailing-record input cleanup. -/
theorem PacketPrefixRequest.budget_le_native (r : PacketPrefixRequest) :
    r.budget ≤ r.native.budget := by
  have hn := r.steps_le
  have hi := r.word_length_le
  have hnative : leadOnes r.native.word = natBitLength r.native.hint := by
    unfold PacketRequest.word
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.native.hint
        (natWord r.native.modulus ++ natWord r.native.values.length ++
          packetStream r.native.width r.native.values)
  have hl : leadOnes r.word = leadOnes r.native.word := r.leading_hint.trans hnative.symm
  unfold PacketPrefixRequest.budget PacketRequest.budget langBudget
  rw [hl]
  dsimp only
  gcongr

/-- `prop:time`, paper/paper.tex: the actual fused
prefix decoder has one linear native-record-count factor and a fixed
polynomial binary-width factor, even when padding leaves unused records. -/
theorem PacketPrefixRequest.budget_le (r : PacketPrefixRequest) :
    r.budget ≤ 10 ^ 12 * (TSK packetCallee + 10) *
      (r.native.values.length + 1) * (r.native.hint + 1) ^ 4 :=
  r.budget_le_native.trans r.native.budget_le

end NearQuarticWires.StageRecovery
