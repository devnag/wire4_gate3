import Proof.Quartic.StagePrintTuple.ReverseState
import Proof.Quartic.StagePrintTuple.SupportPhase
import Proof.Quartic.StagePrintTuple.KernelMaps
import Proof.Quartic.StagePrintTuple.CallPreserve

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the actual
support-selection subprogram runs from the literal reverse-loop state
after its real counter decrement. No variable or serialized request is
supplied separately from the retained actual support. -/
theorem kernelSupport_run (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span done cap : ℕ) (hd : done<data.order.length)
    (hp : supportIndexWordFunction.program.tapeCount ≤ span)
    (hinput : 1000*supportInputMagnitude
      (finiteSupportRequest data.order (reverseSupportIndex data.order done hd)) ≤ cap)
    (hcall : 2*(finiteSupportRequest data.order (reverseSupportIndex data.order done hd)).word.length+2+
      (finiteSupportRequest data.order (reverseSupportIndex data.order done hd)).budget ≤ cap)
    (houtput : (frame (finiteSupportRequest data.order
      (reverseSupportIndex data.order done hd)).output).length+1 ≤ cap) :
    let σ := (data.reverseState r span done).setv 15 (data.order.length-(done+1))
    ∃τ,WXExec cap (supportPhaseProgram
      (kernelPacketMap span kernelSupportSources supportIndexWordFunction.program hp)
      kernelSupportRegisters 15 16 (kernelSite span supportIndexWordFunction.program hp)
      (kernelLocal span 17) 0) σ τ
      (supportPhaseCost (finiteSupportRequest data.order (reverseSupportIndex data.order done hd))) ∧
      SimW (σ.sets (kernelLocal span 17)
        (frame (finiteSupportRequest data.order (reverseSupportIndex data.order done hd)).output)) τ := by
  let σ := (data.reverseState r span done).setv 15 (data.order.length-(done+1))
  let q := finiteSupportRequest data.order (reverseSupportIndex data.order done hd)
  let P := kernelPacketMap span kernelSupportSources supportIndexWordFunction.program hp
  let R := kernelSupportRegisters
  let s := kernelSite span supportIndexWordFunction.program hp
  have hblank : CallBlank supportIndexWordFunction.program s σ :=
    (data.reverseState_blank r span done _ hp).setv 15 _ (by
      intro i;fin_cases i <;> simp [kernelSite,kernelCallRegisters])
  apply supportPhaseProgram_spec cap P R 15 16 s (kernelLocal span 17) 0
    (by simpa [P,s] using kernelPacketMap_input span kernelSupportSources supportIndexWordFunction.program hp)
    q σ hblank
  · intro i;fin_cases i <;> decide
  · intro i;fin_cases i <;> decide
  · change σ.st (kernelLocal span 14)=_
    simp [σ,q,finiteSupportRequest,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · change σ.sh (kernelLocal span 14)=_
    simp [σ,q,finiteSupportRequest,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state,kernelLocal]
  · intro i
    fin_cases i <;> simp [σ,R,kernelSupportRegisters,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state]
  · simp [σ,q,finiteSupportRequest,reverseSupportIndex]
  · simp [σ,q,finiteSupportRequest,MonomialData.reverseState,MonomialData.reverseData,
      KernelData.state]
  · exact kernelSite_out span _ hp 17 (by decide) (by decide)
  · exact kernelSite_ruler_ne span _ hp 17 (by decide)
  · simp [s,kernelSite,kernelCallRegisters]
  · simp [σ,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal]
  · simp [σ,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,kernelLocal]
  · simp [σ,MonomialData.reverseState,MonomialData.reverseData,KernelData.state]
  · exact hinput
  · exact hcall
  · exact houtput

end NearQuarticWires.StageTuple
