import Proof.Quartic.StageRecovery.FramedPair
import Proof.Quartic.StageRecovery.NativeHeaderMachine
import Proof.Quartic.StageRecovery.NativeProducer
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: actual header
concatenation followed by the unchanged native packet is exactly the
existing prefix decoder's literal input word. -/
theorem NativeRequest.header_packet_word (r : NativeRequest) :
    r.header ++ r.table.output = r.prefix.word := by
  rw [r.prefix_word]
  simp only [NativeRequest.header, List.append_assoc]

/-- `prop:time`, paper/paper.tex: both actual
cold calls, constant source copying and one ordered output scan have
additive physical costs before centered prefix recovery. -/
noncomputable def NativeRequest.joinBudget
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeRequest) : ℕ :=
  2 * FramedPair.cost (input := NativeRequest.word) (left := NativeRequest.header)
    (right := fun r => r.table.output) (lb := NativeRequest.headerBudget)
    (rb := nativeProducerBudget h) r + 2

/-- `lem:print`, paper/paper.tex:
the genuine cold header/native join uses only the published Williams
input, real field extraction, actual native table computation and
literal physical frame scans. -/
noncomputable def nativeJoinedWordFunction
    (h : Bindings.Williams14.Williams14_Corollary4_4) :
    WordFunction NativeRequest NativeRequest.word (fun r => frame r.prefix.word)
      (NativeRequest.joinBudget h) := by
  let f := FramedPair.wordFunction nativeHeaderWordFunction (nativeProducerWordFunction h)
  refine ⟨f.program, ?_⟩
  intro r
  obtain ⟨receipt, hr, ho⟩ := f.realizes r
  exact ⟨receipt, hr, by simpa only [r.header_packet_word] using ho⟩

/-- `prop:time`, paper/paper.tex: the literal
native recovery budget includes the real join, full padded-packet input
cleanup and the unchanged centered-prefix decoder. -/
noncomputable def NativeRequest.recoveryBudget
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeRequest) : ℕ :=
  4 * r.joinBudget h + 4 * r.prefix.budget + 12

/-- `lem:print` and `lem:residue`, paper/paper.tex: a complete actual cold native request produces precisely
the canonical centered original-column prefix, including padded tables,
with no raw polynomial-value or prepared-header input and no additional
algorithm assumption beyond the existing published Williams binding. -/
noncomputable def nativeRecoveryWordFunction
    (h : Bindings.Williams14.Williams14_Corollary4_4) :
    WordFunction NativeRequest NativeRequest.word NativeRequest.output (NativeRequest.recoveryBudget h) := by
  let f : WordFunction NativeRequest (fun r => r.prefix.word) NativeRequest.output
      (fun r => r.prefix.budget) :=
    ⟨packetPrefixWordFunction.program, fun r => packetPrefixWordFunction.realizes r.prefix⟩
  exact Program.WordFunction.pipe (nativeJoinedWordFunction h) f

end NearQuarticWires.StageRecovery
