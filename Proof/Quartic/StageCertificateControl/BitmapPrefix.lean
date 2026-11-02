import Proof.Quartic.StageCertTests.FlagRound

/-!
# The sole final crop commutes with every exact signed test

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and the native table order in `lem:print`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open StageCertTests (updatedFlagList)

/-- A strict signed whole-table merge of `sec:algorithm`,
paper/paper.tex, acts independently at every retained
native position, including arbitrary padding and negative entries. -/
theorem updatedFlagList_take (bound : ℕ) (flags : List Bool) (values : List ℤ) (count : ℕ) :
    (updatedFlagList bound flags values).take count=
      updatedFlagList bound (flags.take count) (values.take count) := by
  exact List.take_zipWith

/-- The complete conjunction of Step 2, `sec:algorithm`,
paper/paper.tex, may retain the full native bitmap
through all tests and crop the original-center prefix once. -/
theorem take_fold_updates (tests : List (ℕ×List ℤ)) (flags : List Bool) (count : ℕ) :
    (tests.foldl (fun bits test => updatedFlagList test.1 bits test.2) flags).take count=
      tests.foldl (fun bits test => updatedFlagList test.1 bits (test.2.take count))
        (flags.take count) := by
  induction tests generalizing flags with
  | nil => rfl
  | cons test tests ih =>
    simp only [List.foldl_cons]
    rw [ih,updatedFlagList_take]

end NearQuarticWires.StageCertificateControl
