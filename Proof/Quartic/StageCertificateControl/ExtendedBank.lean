import Proof.Quartic.StageCertificateControl.CountHeader
import Proof.Amplification.RecoveryFocusDock

/-!
# Unused physical tapes in the shared certificate bank

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: a fixed
program may retain extra physical tapes without reading or moving them. -/
def extendedBankProgram (p : Program) (extra : ℕ) : Program where
  tapeCount := p.tapeCount+extra
  stateCount := p.stateCount
  twoTapes := by have := p.twoTapes;omega
  machine := TapeEmbedding.machine extra p.machine
  outputTape := p.outputTape.castAdd extra
  outputFresh := p.outputFresh

/-- `prop:time`, paper/paper.tex: the actual
source occupies the same first tape, and every added tape starts blank. -/
theorem extendedBankProgram_input (p : Program) (extra : ℕ) (word : List Bool) :
    (extendedBankProgram p extra).inputTapes word=
      Fin.addCases (p.inputTapes word) (fun _ : Fin extra => []) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Program.inputTapes,extendedBankProgram]
  · have h : p.tapeCount≠0 := by have := p.twoTapes;omega
    simp [Program.inputTapes,extendedBankProgram,h]

/-- `prop:time`, paper/paper.tex: adding
unused bank tapes preserves the exact output and transition budget.
The extra tapes remain part of the physical program. -/
def extendedBankWordFunction {Request : Type} {input output : Request→List Bool}
    {budget : Request→ℕ} (f : WordFunction Request input output budget) (extra : ℕ) :
    WordFunction Request input output budget where
  program := extendedBankProgram f.program extra
  realizes req := by
    obtain ⟨r,hr,ho⟩ := f.realizes req
    refine ⟨TapeEmbedding.receipt (fun _ : Fin extra => 0) (fun _ => []) r,?_,?_⟩
    · have he := TapeEmbedding.run_embed f.program.machine
        (fun _ : Fin extra => 0) (fun _ => []) (budget req)
        (⟨f.program.machine.start,fun _ => 0,f.program.inputTapes (input req)⟩)
        r hr
      change runFrom (TapeEmbedding.machine extra f.program.machine) (budget req)
        ⟨f.program.machine.start,fun _ => 0,(extendedBankProgram f.program extra).inputTapes (input req)⟩=_
      have hstart : TapeEmbedding.config (fun _ : Fin extra => 0) (fun _ => [])
          (⟨f.program.machine.start,fun _ => 0,f.program.inputTapes (input req)⟩)=
          (⟨f.program.machine.start,fun _ => 0,
            (extendedBankProgram f.program extra).inputTapes (input req)⟩ :
              Configuration (f.program.tapeCount+extra) f.program.stateCount) := by
        apply configuration_ext
        · rfl
        · funext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · simp [TapeEmbedding.config]
          · simp [TapeEmbedding.config]
        · exact (extendedBankProgram_input f.program extra (input req)).symm
      rw [hstart] at he
      exact he
    · simpa only [extendedBankProgram,TapeEmbedding.receipt_tapes_old] using ho

end NearQuarticWires.StageCertificateControl
