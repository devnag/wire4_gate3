import Proof.Quartic.StageMain.FinalField
import Proof.Quartic.StageMain.GreedyTail

/-!
# The literal Step 5 record written by the main pass

Step 4 of `sec:algorithm`, paper/paper.tex,
writes the nine inputs of Step 5 in their prescribed order. The
rational error parameter and two signed totals occupy thirteen
natural-number fields, preceded by the successful-dispatch tag.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift

def printFields : List FinalField → St VV MM
  | [] => skipS
  | x :: xs => .seq x.program (printFields xs)

theorem printFields_run (C : Ctx) (c : Call) (p : Cells.Parameters) (xs : List FinalField)
    (hx : ∀ x ∈ xs, x.Safe) (R : ℕ) (a : DS VV MM) (hc : Cst a) (hs : PrintSource c p a)
    (hW : 2 ≤ C.Wd) (hindex : 46 < 2 ^ C.Wd)
    (hwidth : R + 2 ≤ C.Wd) (hfit : R + 2 < 2 ^ C.Wd)
    (hbits : ∀ x ∈ xs, natBitLength (x.value c p a) ≤ R) :
    Hs C (printFields xs) a (xs.length * (fieldPrintBound c R + 1) + 1) (fun b =>
      b.out = a.out ++ xs.flatMap (fun x => natWord (x.value c p a)) ∧ PrintSource c p b ∧
      (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b sourcePrintScratch) := by
  induction xs generalizing a with
  | nil =>
    refine (skip_spec a).mono (by simp) ?_
    rintro b rfl
    have hf : Fr a (a.set vJ 0) sourcePrintScratch := Fr.set a _ (by simp [sourcePrintScratch])
    exact ⟨by simp, ⟨hs.call, hs.parameters, hs.callCursor, hs.parameterCursor⟩, rfl, Cst.of_fr hc hf (by decide), hf⟩
  | cons x xs ih =>
    unfold printFields
    refine (Hs.seq (t2 := xs.length * (fieldPrintBound c R + 1) + 1)
      (x.run C c p (hx x (by simp)) R a hc hs hW hindex hwidth hfit (hbits x (by simp))) ?_).mono
        (by simp only [List.length_cons]; exact le_of_eq (by ring)) (fun _ h => h)
    rintro b ⟨hbo, hbs, hbrest, hbc, hbfr⟩
    have hvals : ∀ y ∈ xs, y.value c p b = y.value c p a :=
      fun y hy => y.value_frame c p (hx y (by simp [hy])) hbfr
    refine (ih (fun y hy => hx y (by simp [hy])) b hbc hbs
      (fun y hy => by rw [hvals y hy]; exact hbits y (by simp [hy]))).mono le_rfl ?_
    rintro d ⟨hdo, hds, hdrest, hdc, hdfr⟩
    refine ⟨?_, hds, hdrest.trans hbrest, hdc, hbfr.trans hdfr⟩
    rw [hdo, hbo]
    have he := List.flatMap_congr (fun y hy => congrArg natWord (hvals y hy))
    rw [he]
    simp only [List.flatMap_cons, List.append_assoc]

def finalFields : List FinalField :=
  [.arity, .parameter 6, .parameter 17, .parameter 16, .parameter 33,
   .parameter 34, .parameter 35, .register certifiedCount,
   .register consistency, .register vZ, .register acceptanceTotal,
   .register vZ, .register maskTotal]

theorem finalFields_safe : ∀ x ∈ finalFields, x.Safe := by
  intro x hx
  simp only [finalFields, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold FinalField.Safe <;> decide

def printMainRecord : St VV MM := .seq (.op (.emit true)) (printFields finalFields)

theorem printMainRecord_run (C : Ctx) (c : Call) (p : Cells.Parameters)
    (R : ℕ) (a : DS VV MM) (hc : Cst a) (hs : PrintSource c p a)
    (hW : 2 ≤ C.Wd) (hindex : 46 < 2 ^ C.Wd)
    (hwidth : R + 2 ≤ C.Wd) (hfit : R + 2 < 2 ^ C.Wd)
    (hbits : ∀ x ∈ finalFields, natBitLength (x.value c p a) ≤ R) :
    Hs C printMainRecord a (13 * (fieldPrintBound c R + 1) + 3) (fun b =>
      b.out = a.out ++ (true :: finalFields.flatMap (fun x => natWord (x.value c p a))) ∧
      PrintSource c p b ∧
      (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b sourcePrintScratch) := by
  unfold printMainRecord
  refine (Hs.seq (t1 := 1) (t2 := 13 * (fieldPrintBound c R + 1) + 1)
    (Hs.op (OpEx.emit (C := C) true a) rfl) ?_).mono (by omega) (fun _ h => h)
  rintro b rfl
  refine (printFields_run C c p finalFields finalFields_safe R { a with out := a.out ++ [true] }
    ⟨hc.z, hc.one, hc.two⟩ ⟨hs.call, hs.parameters, hs.callCursor, hs.parameterCursor⟩
    hW hindex hwidth hfit (by
      intro x hx
      have he : x.value c p { a with out := a.out ++ [true] } = x.value c p a := by
        cases x <;> rfl
      rw [he]; exact hbits x hx)).mono le_rfl ?_
  rintro d ⟨hdo, hds, hdrest, hdc, hdfr⟩
  have hvals : finalFields.flatMap (fun x => natWord (x.value c p { a with out := a.out ++ [true] })) =
      finalFields.flatMap (fun x => natWord (x.value c p a)) := by
    apply List.flatMap_congr
    intro x _
    cases x <;> rfl
  rw [hvals] at hdo
  exact ⟨by simpa only [List.append_assoc, List.singleton_append] using hdo,
    hds, hdrest, hdc, hdfr⟩

end NearQuarticWires.StageMain.Controller
