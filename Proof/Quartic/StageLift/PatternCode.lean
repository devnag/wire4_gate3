import Proof.Quartic.StagePrint.TranslationLoop
import Proof.Quartic.StageCertTests.PatternParity

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open scoped BigOperators

/-- Step 3 and `sec:walks`, paper/paper.tex: the eight actual sign bits have their exact low-first ordinal. -/
def printPatternCode (pattern : Cycle.SignPattern 4) : ℕ :=
  (finFunctionFinEquiv (fun i : Fin 8 =>
    (⟨(pattern i).toNat, by cases pattern i <;> decide⟩ : Fin 2))).val

/-- Step 3 and `sec:walks`, paper/paper.tex: the decoded ordinal is always one of the literal256 patterns. -/
theorem printPatternCode_lt (pattern : Cycle.SignPattern 4) : printPatternCode pattern < 256 :=
  (finFunctionFinEquiv (fun i : Fin 8 =>
    (⟨(pattern i).toNat, by cases pattern i <;> decide⟩ : Fin 2))).isLt

/-- Step 3 and `sec:walks`, paper/paper.tex: each actual runtime sign-code bit recovers its original
request pattern, with no changed bit or reversed orientation. -/
theorem printPatternCode_testBit (pattern : Cycle.SignPattern 4) (i : Fin 8) :
    (printPatternCode pattern).testBit i.val = pattern i := by
  let f : Fin 8 → Fin 2 := fun j => ⟨(pattern j).toNat, by cases pattern j <;> decide⟩
  have h := congrArg (fun g : Fin 8 → Fin 2 => (g i).val)
    (finFunctionFinEquiv.symm_apply_apply f)
  change printPatternCode pattern / 2 ^ i.val % 2 = (pattern i).toNat at h
  rw [Nat.testBit_eq_decide_div_mod_eq, h]
  cases pattern i <;> decide

/-- Step 3 and `lem:print`, paper/paper.tex: the existing physical binary-prefix reader computes this
same original sign ordinal when fed the eight retained pattern records. -/
theorem binaryPrefix_printPattern (pattern : Cycle.SignPattern 4) :
    StagePrint.Header.binaryPrefix (List.ofFn pattern) 8 = printPatternCode pattern := by
  unfold StagePrint.Header.binaryPrefix
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if (List.ofFn pattern).getD i false then 2 ^ i else 0) 8]
  change (∑ i : Fin 8, if (List.ofFn pattern).getD i.val false then 2 ^ i.val else 0) =
    ∑ i : Fin 8, (pattern i).toNat * 2 ^ i.val
  apply Finset.sum_congr rfl
  intro i _
  have hbit : (List.ofFn pattern).getD i.val false = pattern i := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.getElem_ofFn]
  rw [hbit]
  cases pattern i <;> simp

end NearQuarticWires.StageLift
