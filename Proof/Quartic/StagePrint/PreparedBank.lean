import Proof.Gates.WordPrograms.WMX
import Proof.Wire_3_5.FinalPassWords
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: replacing only a blank ordinary input slot by the real framed request gives exactly the ordinary input tape bank. -/
theorem preparedBank_input {ns nr : ℕ} (p : Program)
    (σ : WState ns nr) (map : Fin p.tapeCount→Fin (ns+1)) (X : Fin (ns+1))
    (offset : ℕ) (word : List Bool)
    (hmap : ∀j,(map j).val=offset+j.val) (hX : X.val=offset)
    (hblank : ∀j,σ.st (map j)=[]) (j : Fin p.tapeCount) :
    (σ.sets X (frame word)).st (map j)=p.inputTapes word j := by
  by_cases hj : j.val=0
  · have hx : map j=X:=by
      apply Fin.ext
      rw [hmap,hj,Nat.add_zero,hX]
    simp only [WState.sets,hx,Function.update_self,Program.inputTapes,hj,ite_true]
  · have hx : map j≠X:=by
      intro h
      have hv:=congrArg Fin.val h
      rw [hmap,hX] at hv
      omega
    simp only [WState.sets,Function.update_of_ne hx,Program.inputTapes,if_neg hj]
    exact hblank j

end NearQuarticWires.StagePrint
