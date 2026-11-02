import Proof.Quartic.StagePrint.CenterCoordinates
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

/-- `imp:printer` and `lem:print`, paper/paper.tex: taking an initial segment retains the literal finite
indices, without an arbitrary order permutation. -/
theorem take_ofFn_castLE {α : Type*} {U R : ℕ} (f : Fin U → α) (hR : R ≤ U) :
    (List.ofFn f).take R = List.ofFn (fun i : Fin R => f (i.castLE hR)) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hR]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

/-- `imp:printer` and `lem:print`, paper/paper.tex: a rectangular native table is cropped by one
prefix operation per row in its existing row-major order. -/
theorem rowMajorCrop_eq {α : Type*} (U R C : ℕ)
    (hR : R ≤ U) (hC : C ≤ U) (f : Fin U → Fin U → α) :
    (((List.ofFn fun i => List.ofFn fun j => f i j).take C).map (fun row => row.take R)).flatten =
      (List.ofFn fun i : Fin C => List.ofFn fun j : Fin R =>
        f (i.castLE hC) (j.castLE hR)).flatten := by
  rw [take_ofFn_castLE _ hC,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact take_ofFn_castLE _ hR

/-- `imp:partition` and `lem:print`, paper/paper.tex: low-row/high-column order is precisely the natural
order of the original center index. -/
theorem centerMajor_ofFn {α : Type*} (R C : ℕ) (f : Fin (R*C) → α) :
    (List.ofFn fun high : Fin C => List.ofFn fun low : Fin R =>
      f ⟨low.val+R*high.val,by
        have hl := low.isLt
        have hh := high.isLt
        nlinarith⟩).flatten = List.ofFn f := by
  simpa only [Nat.add_comm] using (List.ofFn_mul' f).symm

/-- `imp:partition` and `lem:print`, paper/paper.tex: the cropped native stream has exactly the requested
original center census, independent of native square padding. -/
theorem rowMajorCrop_length {α : Type*} (U R C : ℕ)
    (hR : R ≤ U) (hC : C ≤ U) (f : Fin U → Fin U → α) :
    ((((List.ofFn fun i => List.ofFn fun j => f i j).take C).map
      (fun row => row.take R)).flatten).length = R*C := by
  rw [rowMajorCrop_eq U R C hR hC f]
  simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn,
    List.sum_ofFn]
  simp [Nat.mul_comm]

end NearQuarticWires.StageCertTests
