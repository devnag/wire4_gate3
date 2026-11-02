import Proof.Quartic.StagePrintTuple.NativePhaseContract
import Proof.Quartic.StagePrintTuple.CallPreserve

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: native reply
storage, physical reply cursors and its three persistent count registers
are exterior to every reusable genuine callee bank. -/
theorem nativePhaseState_blank (span : ℕ) (r : StageNativeKids.NativeKidsRequest)
    (p : Program) (hp : p.tapeCount ≤ span) (σ : WState (span+29) 32)
    (h : CallBlank p (kernelSite span p hp) σ) :
    CallBlank p (kernelSite span p hp) (nativePhaseState span r σ) := by
  have h18 := kernelSite_out span p hp 18 (by decide) (by decide)
  have h19 := kernelSite_out span p hp 19 (by decide) (by decide)
  have hr18 := kernelSite_ruler_ne span p hp 18 (by decide)
  have hr19 := kernelSite_ruler_ne span p hp 19 (by decide)
  have h13 : ∀i,(kernelSite span p hp).regs i≠13 := by
    intro i;fin_cases i <;> simp [kernelSite,kernelCallRegisters]
  have h24 : ∀i,(kernelSite span p hp).regs i≠24 := by
    intro i;fin_cases i <;> simp [kernelSite,kernelCallRegisters]
  have h25 : ∀i,(kernelSite span p hp).regs i≠25 := by
    intro i;fin_cases i <;> simp [kernelSite,kernelCallRegisters]
  exact ((((((h.sets (kernelLocal span 18) (frame (nativePhasePayload r)) h18 hr18).seth
    (kernelLocal span 18) (frame (nativePhasePayload r)).length h18 hr18).sets
      (kernelLocal span 19) (nativePhasePayload r) h19 hr19).seth
        (kernelLocal span 19) (NearCubicWires.RepairRepresentation.natWord
          (r.toRowContext.nativeKids r.atom).length).length h19 hr19).setv 13
            (r.toRowContext.nativeKids r.atom).length h13).setv 24
              (frame (nativePhasePayload r)).length h24).setv 25 (nativePhasePayload r).length h25

end NearQuarticWires.StageTuple
