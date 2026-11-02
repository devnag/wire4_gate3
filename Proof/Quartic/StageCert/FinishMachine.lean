import Proof.Quartic.StageCert.FinishRun
import Proof.Quartic.StageCert.RecordMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the declared global table
width determines all arithmetic banks used by the certificate finisher. -/
theorem table_context_width (r : CertTableRequest) :
    tableWidth r+4 ≤ (ctxOf recordCallee recordSizes (certTableWord r)).Wd := by
  change tableWidth r+4 ≤ 2^(1*leadOnes (certTableWord r))*16
  have he : leadOnes (certTableWord r) = natBitLength (tableWidth r) := by
    unfold certTableWord
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord (tableWidth r)
        (natWord r.payload.length ++ r.payload ++ natWord (if r.doAppend then 1 else 0) ++
          listWord (listWord momentRecordWord) r.columns)
  rw [he,Nat.one_mul]
  have h := lt_natBitLength (tableWidth r)
  omega

/-- `prop:time`, paper/paper.tex: the actual global
certificate-finisher budget includes every byte operation of the compiled scan. -/
noncomputable def finishBudget (r : CertTableRequest) : ℕ :=
  langBudget recordCallee recordSizes VV MM (certTableWord r)
    (10^7*(r.payload.length+streamWork r.columns+tableWidth r+1)*
      ((ctxOf recordCallee recordSizes (certTableWord r)).Wd+1))

/-- `sec:algorithm`, paper/paper.tex: a physical word
function transforms the complete signed table stream into the exact framed
certificate-stage word. -/
noncomputable def finishMachine : WordFunction CertTableRequest certTableWord certTableOutput finishBudget :=
  wordFunction_of_lang certTableWord certTableOutput recordCallee recordSizes finishProgram
    (fun r => 10^7*(r.payload.length+streamWork r.columns+tableWidth r+1)*
      ((ctxOf recordCallee recordSizes (certTableWord r)).Wd+1)) (by
      intro r
      obtain ⟨b,n,he,hn,hb⟩ := finishProgram_run
        (ctxOf recordCallee recordSizes (certTableWord r)) r rfl (table_context_width r)
      exact ⟨b,n,he,hb,hn⟩) (by
      intro r
      have h := table_context_width r
      change 1 ≤ (ctxOf recordCallee recordSizes (certTableWord r)).Wd
      omega)

/-- `sec:algorithm`, paper/paper.tex: the physical finisher is
specialized to the actual call, witness, column data and stage codecs. -/
noncomputable def finishCallMachine (B1 B2 : ℕ) :
    WordFunction (Call × List Bool)
      (fun r => certTableWord (callTableRequest B1 B2 r.1 r.2))
      (fun r => frame (Program.certWord B1 B2 r.1 r.2))
      (fun r => finishBudget (callTableRequest B1 B2 r.1 r.2)) where
  program := finishMachine.program
  realizes := by
    intro r
    obtain ⟨receipt,he,ho⟩ := finishMachine.realizes (callTableRequest B1 B2 r.1 r.2)
    exact ⟨receipt,he,ho.trans (certTableOutput_call B1 B2 r.1 r.2)⟩

/-- `sec:algorithm`, paper/paper.tex: exact composition of
physical table printing and physical certification gives the required stage
word function, without a certificate-test oracle. -/
noncomputable def certOfTableMachine (B1 B2 : ℕ) (tableBudget : Call × List Bool → ℕ)
    (tables : WordFunction (Call × List Bool) (fun r => Program.prepWord B1 B2 r.1 r.2)
      (fun r => frame (certTableWord (callTableRequest B1 B2 r.1 r.2))) tableBudget) :
    WordFunction (Call × List Bool) (fun r => Program.prepWord B1 B2 r.1 r.2)
      (fun r => frame (Program.certWord B1 B2 r.1 r.2))
      (fun r => 4*tableBudget r+4*finishBudget (callTableRequest B1 B2 r.1 r.2)+12) :=
  Program.WordFunction.pipe tables (finishCallMachine B1 B2)

end NearQuarticWires.StageCert
