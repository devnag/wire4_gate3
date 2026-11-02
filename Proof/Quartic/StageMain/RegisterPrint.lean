import Proof.Quartic.StageMain.EntryEmit

/-!
# Writing the final main-pass scalars

Step 4 of `sec:algorithm`, paper/paper.tex,
writes the Step 5 fields in their literal binary natural-word order.
Each field is copied to the codec register and emitted by its paid
binary printer; all remaining record registers are preserved.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

def printRegister (x : Fin VV) : St VV MM := .seq (.op (.copy t3 x)) emitNatO

def registerPrintScratch : List (Fin VV) := t3 :: emitNatT

theorem printRegister_run (C : Ctx) (x : Fin VV) (hx : t3 ≠ x)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hfit : natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (printRegister x) a (40 * natBitLength (a.env x) + 42) (fun b =>
      b.out = a.out ++ natWord (a.env x) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b registerPrintScratch) := by
  unfold printRegister
  refine (Hs.seq (t1 := 1) (t2 := 40 * natBitLength (a.env x) + 40)
    (hs_copy C t3 x a hx) ?_).mono (by omega) (fun _ h => h)
  rintro b rfl
  have hf : Fr a (a.set t3 (a.env x)) [t3] := Fr.set a _ (by simp)
  have hbc := Cst.of_fr hc hf (by decide)
  refine (emitNatO_spec (C := C) (a.set t3 (a.env x)) hbc hW
    (by simpa only [DS.set_env_self] using hfit)).mono le_rfl ?_
  rintro d ⟨hdout, hdrest, hdc, hdfr⟩
  exact ⟨hdout, hdrest, hdc,
    (hf.weaken (by simp [registerPrintScratch])).trans
      (hdfr.weaken (fun _ hx => List.mem_cons_of_mem _ hx))⟩

def printRegisters : List (Fin VV) → St VV MM
  | [] => skipS
  | x :: xs => .seq (printRegister x) (printRegisters xs)

def registerPrintCost (xs : List (Fin VV)) (a : DS VV MM) : ℕ :=
  (xs.map (fun x => 40 * natBitLength (a.env x) + 43)).sum + 1

theorem printRegisters_run (C : Ctx) (xs : List (Fin VV))
    (hsafe : ∀ x ∈ xs, x ∉ registerPrintScratch)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hfit : ∀ x ∈ xs, natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (printRegisters xs) a (registerPrintCost xs a) (fun b =>
      b.out = a.out ++ xs.flatMap (fun x => natWord (a.env x)) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (vJ :: registerPrintScratch)) := by
  induction xs generalizing a with
  | nil =>
    refine (skip_spec a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp, rfl, Cst.of_fr hc (Fr.set (T := [vJ]) a _ (by simp)) (by decide),
      Fr.set a _ (by simp)⟩
  | cons x xs ih =>
    have hx : t3 ≠ x := by intro he; exact hsafe x (by simp) (by simp [registerPrintScratch, ← he])
    unfold printRegisters
    refine (Hs.seq (t2 := registerPrintCost xs a)
      (printRegister_run C x hx a hc hW (hfit x (by simp))) ?_).mono
        (by simp only [registerPrintCost, List.map_cons, List.sum_cons]; omega) (fun _ h => h)
    rintro b ⟨hbout, hbrest, hbc, hbfr⟩
    have hxenv : ∀ y ∈ xs, b.env y = a.env y :=
      fun y hy => hbfr y (hsafe y (by simp [hy]))
    have hcost : registerPrintCost xs b = registerPrintCost xs a := by
      unfold registerPrintCost
      congr 2
      exact List.map_congr_left (fun y hy => by rw [hxenv y hy])
    have hbits : xs.flatMap (fun y => natWord (b.env y)) =
        xs.flatMap (fun y => natWord (a.env y)) :=
      List.flatMap_congr (fun y hy => by rw [hxenv y hy])
    have hi := ih (fun y hy => hsafe y (by simp [hy])) b hbc
      (fun y hy => by rw [hxenv y hy]; exact hfit y (by simp [hy]))
    rw [hcost] at hi
    refine hi.mono le_rfl ?_
    rintro d ⟨hdout, hdrest, hdc, hdfr⟩
    exact ⟨by rw [hdout, hbits, hbout]; simp only [List.flatMap_cons, List.append_assoc],
      hdrest.trans hbrest, hdc,
      (hbfr.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans hdfr⟩

end NearQuarticWires.StageMain.Controller
