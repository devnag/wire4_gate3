import Proof.Quartic.StagePrintTuple.KernelReverseProgram
import Proof.Quartic.StagePrintTuple.ReverseState
import Proof.Quartic.StagePrintTuple.CallPreserve

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the grouped
native-pool phase consumes the actual original source and the genuine
selected support atom at the literal reverse-loop boundary. The phase
and native machine here are internal composition parameters. -/
theorem kernelNative_run (phase : KernelNativePhase) (hphase : NativePhaseSpec phase)
    {B : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B)
    (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done cap : ℕ) (hd : done<data.order.length)
    (hf : native.program.tapeCount ≤ span)
    (hcap : 10000*nativePhaseMagnitude B
      (StageNativeKids.NativeKidsRequest.ofTerm r data.order[(reverseSupportIndex data.order done hd).val]) ≤ cap) :
    let atom := data.order[(reverseSupportIndex data.order done hd).val]
    let req := StageNativeKids.NativeKidsRequest.ofTerm r atom
    let σ := ((data.reverseState r span done).setv 15 (data.order.length-(done+1))).sets
      (kernelLocal span 17) (frame (finiteSupportRequest data.order
        (reverseSupportIndex data.order done hd)).output)
    ∃τ,WXExec cap (phase native span hf) σ τ
      (1000000*nativePhaseMagnitude B req) ∧ SimW (nativePhaseState span req σ) τ := by
  let atom := data.order[(reverseSupportIndex data.order done hd).val]
  let req := StageNativeKids.NativeKidsRequest.ofTerm r atom
  let σ0 := (data.reverseState r span done).setv 15 (data.order.length-(done+1))
  let σ := σ0.sets (kernelLocal span 17) (frame (finiteSupportRequest data.order
    (reverseSupportIndex data.order done hd)).output)
  have blank0 : CallBlank native.program (kernelSite span native.program hf) σ0 :=
    (data.reverseState_blank r span done _ hf).setv 15 _ (by
      intro i;fin_cases i <;> simp [kernelSite,kernelCallRegisters])
  have blank : CallBlank native.program (kernelSite span native.program hf) σ :=
    blank0.sets _ _ (kernelSite_out span _ hf 17 (by decide) (by decide))
      (kernelSite_ruler_ne span _ hf 17 (by decide))
  apply hphase native span hf cap req σ blank
  · intro i
    fin_cases i <;> simp [σ,σ0,req,atom,finiteSupportRequest_output,nativePhaseSource,
      StageNativeKids.NativeKidsRequest.ofTerm,StageNativeKids.NativeKidsRequest.contextWord,
      MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
      TermCutRequest.preparedLoadedSource,TermCutRequest.preparedFields,kernelLocal,
      kernelNativeSources,TermCutRequest.contextWord]
  · intro i
    fin_cases i <;> simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal,kernelNativeSources]
  · simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal]
  · simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal]
  · simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal]
  · simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal]
  · intro i
    fin_cases i <;> simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
  · simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
  · simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
  · simp [σ,σ0,MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
  · exact hcap

end NearQuarticWires.StageTuple
