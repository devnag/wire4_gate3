import Proof.Quartic.StageRecovery.ModPointProgram
import Proof.Quartic.StageRecovery.PacketRequest

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the modular point
evaluator's cold binary workspace depends on its structural hint. -/
def pointSizes : Sz := ⟨64, 1, 0, 0, 0, 0⟩

/-- `prop:time`, paper/paper.tex: the original request
header initializes sufficient binary stack workspace with an actual
ordinary-machine setup pass. -/
theorem ModPointRequest.context_width (r : ModPointRequest) :
    64 * (r.source.hint + 1) ≤ (ctxOf packetCallee pointSizes r.word).Wd := by
  have hl : leadOnes r.word = natBitLength r.source.hint := by
    unfold ModPointRequest.word
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.source.hint
        (natWord r.source.modulus ++ natWord r.point ++
          NearCubicGates.Close.Interfaces.Formats.formulaWord ⟨r.source.arity, r.source.formula⟩)
  change 64 * (r.source.hint + 1) ≤ 2 ^ (1 * leadOnes r.word) * 64
  rw [hl, Nat.one_mul]
  have h := lt_natBitLength r.source.hint
  omega

/-- `prop:time`, paper/paper.tex: the actual modular
formula point budget includes setup, every binary source operation,
the complete original token stream and final head/register return. -/
noncomputable def ModPointRequest.budget (r : ModPointRequest) : ℕ :=
  langBudget packetCallee pointSizes VV MM r.word r.steps

/-- `lem:print`, paper/paper.tex: a genuine cold-input
ordinary word function evaluates the literal integer Formula modulo
the actual recovery modulus on a specified Boolean characteristic point. -/
noncomputable def modularPointWordFunction :
    WordFunction ModPointRequest ModPointRequest.word
      (fun r => natWord r.value) ModPointRequest.budget :=
  wordFunction_of_lang ModPointRequest.word (fun r => natWord r.value)
    packetCallee pointSizes modularPointProgram ModPointRequest.steps (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := modularPointProgram_spec
        (ctxOf packetCallee pointSizes r.word) r rfl r.context_width
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      have h := r.context_width
      change 1 ≤ (ctxOf packetCallee pointSizes r.word).Wd
      omega)

end NearQuarticWires.StageRecovery
