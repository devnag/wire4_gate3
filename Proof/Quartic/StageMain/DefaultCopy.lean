import Proof.Quartic.StageMain.MarkedOutput
import Proof.Gates.Cells.Kit

/-!
# Copying the six scalar fields of a completed call

The default cases of `sec:params`, paper/paper.tex, pass their completed interval through Step 4. Six actual
binary reads and writes copy precisely that interval, leaving any
field-cache suffix unread and charging every codec operation.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

def copyRawNatural : St VV MM := .seq rdNatI emitNatO

theorem copyRawNatural_run (C : Ctx) (v : ℕ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip = natWord v ++ rest)
    (hwidth : natBitLength v + 2 ≤ C.Wd) :
    Hs C copyRawNatural a (70 * natBitLength v + 71) (fun b =>
      b.out = a.out ++ natWord v ∧ b.ip = a.ip + (natWord v).length ∧
      (b.ram, b.rc, b.kin, b.kout, b.kc) = (a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b) := by
  unfold copyRawNatural
  refine (Hs.seq (t2 := 40 * natBitLength v + 40) (rdNatI_spec a hc v rest hin hwidth) ?_).mono
    (by omega) (fun _ h => h)
  rintro b ⟨hbv, _hbwidth, hbip, hbrest, hbfr⟩
  have hbc := cst_fr hc hbfr
  have he := emitNatO_spec (C := C) b hbc (by omega)
    (by rw [hbv]; exact hwidth.trans_lt Nat.lt_two_pow_self)
  rw [hbv] at he
  refine he.mono le_rfl ?_
  rintro d ⟨hdout, hdrest, hdc, _hdfr⟩
  rcases (by simpa only [Prod.mk.injEq] using hbrest) with ⟨hbo, hbram, hbrc, hbkin, hbkout, hbkc⟩
  rcases (by simpa only [Prod.mk.injEq] using hdrest) with ⟨hdi, hdram, hdrc, hdkin, hdkout, hdkc⟩
  exact ⟨by rw [hdout, hbo], hdi.trans hbip,
    by rw [hdram, hdrc, hdkin, hdkout, hdkc, hbram, hbrc, hbkin, hbkout, hbkc], hdc⟩

def copyRawNaturals : ℕ → St VV MM
  | 0 => skipS
  | n + 1 => .seq copyRawNatural (copyRawNaturals n)

def copyRawCost (xs : List ℕ) : ℕ :=
  (xs.map (fun v => 70 * natBitLength v + 72)).sum + 1

theorem copyRawNaturals_run (C : Ctx) (xs : List ℕ) (rest : List Bool)
    (hwidth : ∀ v ∈ xs, natBitLength v + 2 ≤ C.Wd)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip = xs.flatMap natWord ++ rest) :
    Hs C (copyRawNaturals xs.length) a (copyRawCost xs) (fun b =>
      b.out = a.out ++ xs.flatMap natWord ∧ b.ip = a.ip + (xs.flatMap natWord).length ∧
      (b.ram, b.rc, b.kin, b.kout, b.kc) = (a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b) := by
  induction xs generalizing a with
  | nil =>
    refine (skip_spec a).mono (by simp [copyRawCost]) ?_
    rintro b rfl
    exact ⟨by simp, by simp, rfl,
      Cst.of_fr hc (Fr.set (T := [vJ]) a _ (by simp)) (by decide)⟩
  | cons v xs ih =>
    have hinput : C.inp.drop a.ip = natWord v ++ (xs.flatMap natWord ++ rest) := by
      simpa only [List.flatMap_cons, List.append_assoc] using hin
    refine (Hs.seq (t2 := copyRawCost xs)
      (copyRawNatural_run C v _ a hc hinput (hwidth v (by simp))) ?_).mono
      (by simp only [copyRawCost, List.map_cons, List.sum_cons]; omega) (fun _ h => h)
    rintro b ⟨hbo, hbi, hbrest, hbc⟩
    refine (ih (fun v hv => hwidth v (by simp [hv])) b hbc (by rw [hbi]; exact drop_adv hinput)).mono le_rfl ?_
    rintro d ⟨hdo, hdi, hdrest, hdc⟩
    exact ⟨by rw [hdo, hbo]; simp only [List.flatMap_cons, List.append_assoc],
      by rw [hdi, hbi]; simp only [List.flatMap_cons, List.length_append, Nat.add_assoc],
      hdrest.trans hbrest, hdc⟩

end NearQuarticWires.StageMain.Controller
