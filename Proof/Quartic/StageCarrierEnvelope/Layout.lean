import Proof.Quartic.StageCarrierEnvelope.Bank
import Proof.Quartic.StageCarrierEnvelope.Loaded

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: raw first
modulus, original carrier and real metadata reply occupy disjoint
tapes, with a fourth fresh tape for the immutable output envelope. -/
def sourceMap (p : Program) : Fin 4↪Fin (p.tapeCount+4) where
  toFun:=![1,0,bankMap p.tapeCount p.outputTape,bankOut p.tapeCount]
  inj':=by
    intro i j h
    have hh:=congrArg Fin.val h
    fin_cases i <;> fin_cases j <;>
      simp [bankMap,bankOut] at hh ⊢ <;> omega

/-- `lem:print`, paper/paper.tex: the
layout uses the two actual source tapes and the actual callee output. -/
theorem sourceMap_values (p : Program) :
    sourceMap p 0=1 ∧ sourceMap p 1=0 ∧
    sourceMap p 2=bankMap p.tapeCount p.outputTape ∧ sourceMap p 3=bankOut p.tapeCount := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end NearQuarticWires.StageCarrierEnvelope
