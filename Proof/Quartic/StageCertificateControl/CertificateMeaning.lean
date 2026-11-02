import Proof.Quartic.StageCertificateControl.BitmapPrefix
import Proof.Quartic.StageCertificateControl.TestFold
import Proof.Quartic.StageCertTests.ActualPlan

/-!
# The complete native bitmap means the literal column certificate

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open StageCertTests (updatedFlagList updateFlags)

/-- A whole signed test of `sec:algorithm`, paper/paper.tex, has the same indexed conjunction in finite-function and
physical ordered-list form. -/
theorem updatedFlagList_ofFn {Z : ℕ} (bound : ℕ) (flags : Fin Z→Bool) (values : Fin Z→ℤ) :
    updatedFlagList bound (List.ofFn flags) (List.ofFn values)=
      List.ofFn (fun z => flags z && decide (values z<(bound:ℤ))) := by
  apply List.ext_getElem
  · simp [updatedFlagList]
  · intro i h1 h2
    simp [updatedFlagList]

/-- The sole final native crop of `sec:algorithm`, paper/paper.tex, commutes with the full signed conjunction, while every
padding column remains present in the actual preceding computation. -/
theorem nativeTestFlags_take (tests : List NativeTest) (flags : List Bool) (keep : ℕ) :
    (nativeTestFlags tests flags).take keep=
      tests.foldl (fun bits test => updatedFlagList test.bound bits (test.values.take keep))
        (flags.take keep) := by
  induction tests generalizing flags with
  | nil => rfl
  | cons test tests ih =>
    change (nativeTestFlags tests (updatedFlagList test.bound flags test.values)).take keep=_
    rw [ih,updatedFlagList_take]
    rfl

/-- The complete whole-table conjunction of `sec:algorithm`,
paper/paper.tex, preserves the exact test-major order when
native original-column prefixes realize the literal signed records. -/
theorem fold_native_prefix_ofFn {Z : ℕ} (tests : List NativeTest)
    (tables : List (Fin Z→StageCert.MomentRecord))
    (hreal : List.Forall₂ (fun test table =>
      test.values.take Z=List.ofFn (fun z => (table z).1) ∧
      ∀ z,(table z).2=test.bound) tests tables) (flags : Fin Z→Bool) :
    tests.foldl (fun bits test => updatedFlagList test.bound bits (test.values.take Z))
      (List.ofFn flags)=List.ofFn (tables.foldl updateFlags flags) := by
  induction hreal generalizing flags with
  | nil => rfl
  | @cons test table tests tables h ht ih =>
    simp only [List.foldl_cons]
    rw [h.1,updatedFlagList_ofFn]
    have hf : (fun z => flags z && decide ((table z).1<(test.bound:ℤ)))=updateFlags flags table := by
      funext z
      simp only [updateFlags,StageCert.recordPass,h.2]
    rw [hf]
    exact ih _

/-- The exact interface between `lem:print` and Step 2,
paper/paper.tex: when each ordered
native prefix is the corresponding original signed moment table,
the actual full-size fold and sole final crop yield precisely the
literal column-certificate bitmap. This requires no certificate
hypothesis on the witness or on any original column. -/
theorem nativeFlags_eq_certifiedBits (c : NearCubicGates.Close.Interfaces.Call)
    {p : Cells.Parameters} (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (tests : List NativeTest) (count : ℕ) (hcount : 2^(c.n-p.k)≤count)
    (hreal : List.Forall₂ (fun test kind =>
      test.bound=StageCertTests.actualTestThreshold p kind ∧
      test.values.take (2^(c.n-p.k))=List.ofFn (fun z =>
        (StageCertTests.actualTestTable c hs w kind z).1))
      tests (StageCertTests.actualTestPlan c p)) :
    (nativeTestFlags tests (List.replicate count true)).take (2^(c.n-p.k))=
      Program.certifiedBits (Builder.cellCall c hs w) := by
  have ht : List.Forall₂ (fun test (table : Fin (2^(c.n-p.k))→StageCert.MomentRecord) =>
      test.values.take (2^(c.n-p.k))=List.ofFn (fun z => (table z).1) ∧
      ∀ z,(table z).2=test.bound)
      tests ((StageCertTests.actualTestPlan c p).map (StageCertTests.actualTestTable c hs w)) := by
    generalize StageCertTests.actualTestPlan c p=kinds at hreal ⊢
    induction hreal with
    | nil => exact .nil
    | @cons test kind tests kinds h ht ih =>
      exact .cons ⟨h.2,fun z => (StageCertTests.actualTestTable_threshold c hs w kind z).trans h.1.symm⟩ ih
  rw [nativeTestFlags_take]
  have hinit : (List.replicate count true).take (2^(c.n-p.k))=
      List.ofFn (fun _ : Fin (2^(c.n-p.k)) => true) := by
    simp only [List.take_replicate,Nat.min_eq_left hcount,List.ofFn_const]
  rw [hinit,fold_native_prefix_ofFn _ _ ht]
  exact StageCertTests.actualFlags_eq_certifiedBits c hs w

end NearQuarticWires.StageCertificateControl
