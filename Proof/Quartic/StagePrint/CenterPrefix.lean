import Proof.Quartic.StagePrint.CenterCoordinates
import Proof.Quartic.StageCertTests.CropOrder
import Proof.Gates.TabMachine.Back

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicGates.Close.TabMachine

/-- `imp:partition` and `lem:print`, paper/paper.tex: a square native stream cropped at a whole-row boundary retains exactly the original high-half prefix. -/
theorem native_square_prefix {α : Type*} (U C : ℕ) (hC : C≤U)
    (g : Fin U→Fin U→α) :
    ((List.ofFn fun high=>List.ofFn fun low=>g high low).flatten).take (U*C)=
      (List.ofFn fun high : Fin C=>List.ofFn fun low : Fin U=>g (high.castLE hC) low).flatten := by
  let rows:=List.ofFn fun high : Fin U=>List.ofFn fun low : Fin U=>g high low
  have hh : ((rows.map List.length).take C).sum=U*C := by
    have he : rows.map List.length=List.replicate U U := by
      simp [rows,List.map_ofFn,Function.comp_def]
    rw [he]
    simp [Nat.min_eq_left hC,Nat.mul_comm]
  change rows.flatten.take (U*C)=_
  rw [←hh,List.take_sum_flatten,StageCertTests.take_ofFn_castLE]

/-- `imp:partition` and `lem:print`, paper/paper.tex: after the separated halves are swapped, the valid row-major prefix is exactly low-row/high-column center-index order, with no later permutation. -/
theorem native_square_prefix_centers (U C : ℕ) (hC : C≤U)
    (g : Fin U→Fin U→ℤ) (f : Fin (U*C)→ℤ)
    (h : ∀high : Fin C,∀low : Fin U,
      g (high.castLE hC) low=f ⟨low.val+U*high.val,by
        have hl:=low.isLt
        have hr:=high.isLt
        nlinarith⟩) :
    (pvals false g).take (U*C)=List.ofFn f := by
  unfold pvals
  simp only [Bool.false_eq_true,if_false]
  rw [native_square_prefix U C hC]
  have he : (List.ofFn fun high : Fin C=>List.ofFn fun low : Fin U=>g (high.castLE hC) low)=
      List.ofFn (fun high : Fin C=>List.ofFn fun low : Fin U=>
        f ⟨low.val+U*high.val,by
          have hl:=low.isLt
          have hr:=high.isLt
          nlinarith⟩) := by
    apply congrArg List.ofFn
    funext high
    apply congrArg List.ofFn
    funext low
    exact h high low
  rw [he]
  exact StageCertTests.centerMajor_ofFn U C f

end NearQuarticWires.StagePrint
