import Proof.Quartic.StagePrintTuple.KernelMonomialPrepare
import Proof.Quartic.StagePrintTuple.TermStageCost
import Proof.Quartic.StagePrintTuple.ReverseLoop
import Proof.Quartic.StageTupleMonomialFinish.Final

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: one fixed
actual monomial program reads the original source, prepares real
caches, performs the full original-child reverse loop and appends its
signed stacked cuts before restoring the next complete Terms boundary. -/
noncomputable def termStageProgram {B : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B)
    (span : ℕ) (hn : native.program.tapeCount ≤ span)
    (hc : coefficientWordFunction.program.tapeCount ≤ span)
    (hs : supportIndexWordFunction.program.tapeCount ≤ span)
    (ht : tupleRecordPrinter.program.tapeCount ≤ span)
    (hstack : stackRecordPrinter.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  .seq (monomialAcquireProgram (kernelExternalMap span kernelMonomialSources) kernelMonomialRegisters)
    (.seq (monomialPrepareProgram span hc)
      (.seq (kernelReverseLoop StageTupleNativePhase.nativePhaseProgram native span hn hs ht)
        (StageTupleMonomialFinish.monomialFinishProgram span hstack)))

end NearQuarticWires.StageTuple
