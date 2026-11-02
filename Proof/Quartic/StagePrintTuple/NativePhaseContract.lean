import Proof.Quartic.StagePrintTuple.KernelMaps
import Proof.Quartic.StagePrintTuple.CallInput
import Proof.Quartic.StageNativeKids.Request

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the five real
retained source payloads determine the exact existing native-pool
request, with no selected row or compiled pool among its inputs. -/
def nativePhaseSource (r : StageNativeKids.NativeKidsRequest) : Fin 5→List Bool :=
  ![callWord r.header.call,(StagePrint.Header.baseHeaderValues r.header).flatMap natWord,
    r.contextWord,natWord r.atom.val,natWord r.outputWidth]

/-- `lem:print`, paper/paper.tex: a native-pool
reply carries its genuinely computed original-child count before all
ordered signed native row fields. -/
def nativePhasePayload (r : StageNativeKids.NativeKidsRequest) : List Bool :=
  natWord (r.toRowContext.nativeKids r.atom).length++
    fieldsRecs r.outputWidth (r.toRowContext.nativeKids r.atom)

/-- `lem:print`, paper/paper.tex: the exact
native phase leaves both literal reply tapes, the parsed original
child count and two measured copy-length counters while preserving
all other source, tuple and output state components. -/
def nativePhaseState (span : ℕ) (r : StageNativeKids.NativeKidsRequest)
    (σ : WState (span+29) 32) : WState (span+29) 32 :=
  ((((((σ.sets (kernelLocal span 18) (frame (nativePhasePayload r))).seth
    (kernelLocal span 18) (frame (nativePhasePayload r)).length).sets
    (kernelLocal span 19) (nativePhasePayload r)).seth (kernelLocal span 19)
      (natWord (r.toRowContext.nativeKids r.atom).length).length).setv 13
        (r.toRowContext.nativeKids r.atom).length).setv 24
          (frame (nativePhasePayload r)).length).setv 25 (nativePhasePayload r).length

/-- `prop:time`, paper/paper.tex: the actual
native-phase source magnitude contains the genuine callee clock and
only an additive quadratic cost for decoding its actual child count. -/
def nativePhaseMagnitude (budget : StageNativeKids.NativeKidsRequest→ℕ)
    (r : StageNativeKids.NativeKidsRequest) : ℕ :=
  r.word.length+budget r+((r.toRowContext.nativeKids r.atom).length+1)^2+1

/-- `lem:print` and `prop:time`, paper/paper.tex: five genuine source frames on a reusable blank call
bank suffice for the complete native source/call/count phase. Every
copy counter is physically obtained, with no callee-length observer. -/
abbrev NativePhaseSpec
    (program : {B : StageNativeKids.NativeKidsRequest→ℕ}→
      (f : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
        StageNativeKids.NativeKidsRequest.output B)→(span : ℕ)→
        f.program.tapeCount ≤ span→WMX (span+29) 32) : Prop :=
  ∀ {B} (f : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B) (span : ℕ) (hf : f.program.tapeCount ≤ span)
    (cap : ℕ) (r : StageNativeKids.NativeKidsRequest) (σ : WState (span+29) 32),
    CallBlank f.program (kernelSite span f.program hf) σ →
    (∀i,σ.st (kernelLocal span (kernelNativeSources i))=frame (nativePhaseSource r i)) →
    (∀i,σ.sh (kernelLocal span (kernelNativeSources i))=0) →
    σ.st (kernelLocal span 18)=[] → σ.sh (kernelLocal span 18)=0 →
    σ.st (kernelLocal span 19)=[] → σ.sh (kernelLocal span 19)=0 →
    (∀i:Fin 10,σ.val ⟨i.val,by omega⟩=0) →
    σ.val 13=0 → σ.val 24=0 → σ.val 25=0 →
    10000*nativePhaseMagnitude B r ≤ cap →
    ∃τ,WXExec cap (program f span hf) σ τ (1000000*nativePhaseMagnitude B r) ∧
      SimW (nativePhaseState span r σ) τ

end NearQuarticWires.StageTuple
