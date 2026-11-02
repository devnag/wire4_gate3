import Proof.Quartic.StageCompiledTerms.BatchCodec
import Proof.Quartic.StageCompiledTerms.AnswerCopy
import Proof.Gates.Expand.PolyTabPack
import Proof.Quartic.Control.GammaControl

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Expand.PolyTab
open NearQuarticWires.Control NearQuarticWires.Reconstruct.Batch

/-- `prop:time`, paper/paper.tex: the maximum
actual per-packet clock bounds each reused compiler invocation; this
proof quantity is neither an input field nor a runtime budget oracle. -/
noncomputable def compilerMaximum {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  ((walkRequests r).map packetCompilerBudget).foldr max 0

/-- `prop:time`, paper/paper.tex: every
physically scheduled original packet obeys the common batch clock. -/
theorem compilerMaximum_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (w : WalkRequest B1 B2) (hw : w∈walkRequests r) :
    packetCompilerBudget w≤compilerMaximum r :=
  List.le_max_of_le (List.mem_map.mpr ⟨w,hw,rfl⟩) le_rfl

/-- `prop:time`, paper/paper.tex: every call,
encoded input/tag copy, compiler answer and bank reset is charged. -/
noncomputable def compiledBatchSteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  batchCost (batchContext r) walkTag walkInput walkAnswer (compilerMaximum r)
    (fun w=>answerCopyCost (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2))) (walkRequests r)

/-- `prop:time`, paper/paper.tex: actual
source/output bytes and the common per-call clock bound finite bank
and tally counters without squaring the compiler's family census. -/
noncomputable def compiledBatchCapacity {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  100*((actualCarrier r).batchWord.length+(StagePrint.TermsCarrier.word r).length+compilerMaximum r+10)

/-- Step 3 and `lem:print`, paper/paper.tex: one fixed ordinary batch compiler consumes every
actual tagged packet, calls its real modular compiler on the reused
bank and writes exactly the original compiled-Terms carrier. -/
noncomputable def compiledBatchWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) (fun r=>(actualCarrier r).batchWord)
      (fun r=>frame (StagePrint.TermsCarrier.word r)) (fun r=>2*compiledBatchSteps r+2) :=
  wordFunction_of_ideal
    (batchP (packetCompilerWordFunction B1 B2).program
      (answerCopier (packetCompilerWordFunction B1 B2).program))
    (cOUT _) (by simp [cOUT]) compiledBatchCapacity (fun _ _=>0) compiledBatchSteps
    (fun _=>le_rfl) (by
      intro r
      let f:=packetCompilerWordFunction B1 B2
      have hBudget : ∀ w∈walkRequests r,packetCompilerBudget w≤compilerMaximum r:=
        compilerMaximum_bound r
      have hCopy : ∀ w∈walkRequests r,∀ a : WState (cns f.program.tapeCount) lnr,
          a.st (cbank _ f.program.outputTape)=walkAnswer w→
          a.sh (cbank _ f.program.outputTape)=0→a.sh (cT _)=(a.st (cT _)).length→
          (∀ i,a.val (cR i)=0)→
          WExec (compiledBatchCapacity r) (answerCopier f.program) a
            (appendT a (cT _) (Streaming.marks (walkAnswer w)))
            (answerCopyCost (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2))) := by
        intro w hw a ha hh hout hz
        have hlen:=Control.output_length_le f w
        have hbud:=hBudget w hw
        apply answerCopier_spec _ f.program _ a ha hh hout hz
        unfold compiledBatchCapacity
        change (walkAnswer w).length≤packetCompilerBudget w+1 at hlen
        change 2*(walkAnswer w).length+1≤_
        omega
      obtain ⟨final,hrun,hout⟩:=batchP_exec (compiledBatchCapacity r) f (answerCopier f.program)
        (answerCopier_avoids f.program) walkTag
        (fun w=>answerCopyCost (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2)))
        (compilerMaximum r) (batchContext r) (walkRequests r) hBudget hCopy (by
          change 10*((frame (batchContext r)++NearCubicGates.Close.Interfaces.listWord
            (fun w=>frame (walkTag w)++frame (walkInput w)) (walkRequests r)).length+
              (batchOut (batchContext r) walkTag walkAnswer (walkRequests r)).length+
                compilerMaximum r+10)≤compiledBatchCapacity r
          rw [←actual_batch_input,actual_batch_output]
          unfold compiledBatchCapacity
          omega)
      change NearCubicGates.Close.WordPrograms.WXExec (compiledBatchCapacity r)
        (batchP f.program (answerCopier f.program))
        (gammaStart f.program.tapeCount
          (frame (batchContext r)++NearCubicGates.Close.Interfaces.listWord
            (fun w=>frame (walkTag w)++frame (walkInput w)) (walkRequests r)))
        final (compiledBatchSteps r) at hrun
      change final.st (cOUT _)=frame (batchOut (batchContext r) walkTag walkAnswer (walkRequests r)) at hout
      rw [←actual_batch_input] at hrun
      rw [actual_batch_output] at hout
      exact ⟨rfl,final,hrun,hout⟩)

end NearQuarticWires.StageCompiledTerms
