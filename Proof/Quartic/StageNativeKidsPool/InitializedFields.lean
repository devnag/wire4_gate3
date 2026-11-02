import Proof.Quartic.StageNativeKidsPool.InitializeReady

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: the
actual initialization's raw prefix and output byte counter agree
exactly, before the original-child row loop begins. -/
theorem initialized_prefix (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (σ : WState (streams counter row) 16)
    (h : Counted F width countBudget counter row q σ) :
    (initialized counter row (F q).count (width q) σ).st ⟨14,by unfold streams;omega⟩=
        natWord (F q).count++natWord (width q) ∧
      (initialized counter row (F q).count (width q) σ).val (10 : Fin 16)=
        (natWord (F q).count++natWord (width q)).length := by
  have hh:=(h.small ⟨14,by unfold streams;omega⟩ (by change 14<20;omega)).1
  have hz : σ.st (⟨14,by unfold streams;omega⟩ : Fin (streams counter row+1))=[]:=by
    simpa [loaded,lens] using hh
  constructor
  · simp [initialized,appendO,hz]
  · simp [initialized,appendO,h.registers]

/-- `lem:print`, paper/paper.tex: the
fresh final framing tape is untouched by actual count initialization. -/
theorem initialized_final (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (σ : WState (streams counter row) 16)
    (h : Counted F width countBudget counter row q σ) :
    (initialized counter row (F q).count (width q) σ).st ⟨15,by unfold streams;omega⟩=[] ∧
      (initialized counter row (F q).count (width q) σ).sh ⟨15,by unfold streams;omega⟩=0 := by
  have hh:=h.small ⟨15,by unfold streams;omega⟩ (by change 15<20;omega)
  have hc : (⟨15,by unfold streams;omega⟩ : Fin (streams counter row+1))≠
      counterMap counter row counter.outputTape:=
    (counterMap_not_small _ _ _ _ (by change 15<20;omega)).symm
  constructor
  · simpa [initialized,appendO,loaded,lens] using hh.1
  · simpa [initialized,appendO,Function.update_of_ne hc] using hh.2

end NearQuarticWires.StageNativeKidsPool
