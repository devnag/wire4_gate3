import Proof.Quartic.StagePrintTuple.KernelMaps
import Proof.Quartic.StagePrintTuple.CartesianStep
import Proof.Quartic.StagePrintTuple.CounterUpdate
import Proof.Quartic.StagePrintTuple.RecordEnd
import Proof.Quartic.StagePrintTuple.FrameErase
import Proof.Quartic.StagePrintTuple.SupportPhase
import Proof.Quartic.StagePrintTuple.NativeCleanup
import Proof.Quartic.StagePrintTuple.NativePhaseContract
import Proof.Quartic.StageTupleInputs.NativeProgram
import Proof.Quartic.StageTupleInputs.SupportProgram
import Proof.Quartic.StageNativeKids.Request
import Proof.Quartic.StageGamma.Unframe
import Proof.Gates.Codec.Unframe

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: a fixed finite
sequence of actual source, call, tuple and cleanup programs executes in
literal order with every sequence transition included. -/
def kernelSequence {ns nr : ℕ} : List (WMX ns nr)→WMX ns nr
  | [] => .skip
  | p::ps => .seq p (kernelSequence ps)

/-- `lem:print`, paper/paper.tex: the native
source/call/count phase has the exact grouped physical signature; its
actual concrete implementation is substituted before the public printer. -/
abbrev KernelNativePhase :=
  {B : StageNativeKids.NativeKidsRequest→ℕ}→
    (f : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B)→(span : ℕ)→
        f.program.tapeCount ≤ span→WMX (span+29) 32

/-- `lem:print`, paper/paper.tex: one actual
reverse-support iteration selects the genuine source atom, computes its
native original-child pool, forms the literal next Cartesian segment,
updates real counts and erases the three finite variable-local caches. -/
noncomputable def kernelReverseBody (phase : KernelNativePhase)
    {nativeBudget : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output nativeBudget)
    (span : ℕ) (hNative : native.program.tapeCount ≤ span)
    (hSupport : supportIndexWordFunction.program.tapeCount ≤ span)
    (hTuple : tupleRecordPrinter.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  let ss := kernelSite span supportIndexWordFunction.program hSupport
  let st := kernelSite span tupleRecordPrinter.program hTuple
  .seq (supportPhaseProgram
      (kernelPacketMap span kernelSupportSources supportIndexWordFunction.program hSupport)
      kernelSupportRegisters 15 16 ss (kernelLocal span 17) 0)
    (.seq (phase native span hNative)
      (.seq (cartesianStepProgram
          (kernelPacketMap span kernelCartesianSources tupleRecordPrinter.program hTuple)
          kernelCartesianRegisters st)
        (.seq (tupleCounterProgram kernelCounterRegisters) (nativeCleanupProgram span))))

/-- `lem:print`, paper/paper.tex: the actual
counted support loop decrements the physically parsed reverse index
before each source selection, retaining ascending-support Cartesian
order through child-first prepending. -/
noncomputable def kernelReverseLoop (phase : KernelNativePhase) {nativeBudget : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output nativeBudget)
    (span : ℕ) (hNative : native.program.tapeCount ≤ span)
    (hSupport : supportIndexWordFunction.program.tapeCount ≤ span)
    (hTuple : tupleRecordPrinter.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  .whr 15 (.seq (.wm (.dec 15)) (kernelReverseBody phase native span hNative hSupport hTuple))

end NearQuarticWires.StageTuple
