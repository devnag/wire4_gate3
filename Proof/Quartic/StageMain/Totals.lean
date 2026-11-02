import Proof.Gates.Cells.Arith

/-!
# The sampled main-pass counters

Step 4 of `sec:algorithm`, paper/paper.tex, forms the
mask total and the acceptance-times-mask total over certified columns.
The ordinary controller adds one precisely for the corresponding
Boolean event; all other registers and streams are preserved.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicGates.Close.Cells

def certifiedCount : Fin VV := 100
def acceptanceTotal : Fin VV := 101
def maskTotal : Fin VV := 102
def certifiedFlag : Fin VV := 103
def predicateFlag : Fin VV := 104
def maskFlag : Fin VV := 105
def sampleCounter : Fin VV := 106
def columnCounter : Fin VV := 107

def addAcceptance : St VV MM :=
  .ite (.eq predicateFlag v1) (.op (.inc acceptanceTotal)) skipS

theorem addAcceptance_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (pred : Bool) (hp : a.env predicateFlag = pred.toNat)
    (hfit : a.env acceptanceTotal + 1 < 2 ^ C.Wd) :
    Hs C addAcceptance a 2 (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal + pred.toNat ∧
      Same a b ∧ Cst b ∧ Fr a b [acceptanceTotal, vJ]) := by
  refine Hs.ite (c := .eq predicateFlag v1) (show predicateFlag ≠ v1 by decide) ?_ ?_
  · intro he
    have ht : pred = true := by
      revert he
      simp only [Cnd.eval, hp, hc.one]
      cases pred <;> simp
    refine (hs_inc C acceptanceTotal a hfit).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [ht], Same.set _ _ _,
      Cst.of_fr hc (Fr.set a _ (by simp : acceptanceTotal ∈ [acceptanceTotal, vJ])) (by decide),
      Fr.set a _ (by simp)⟩
  · intro he
    have ht : pred = false := by
      revert he
      simp only [Cnd.eval, hp, hc.one]
      cases pred <;> simp
    refine (skip_spec a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [ht, DS.set_env_ne _ _ (by decide : acceptanceTotal ≠ vJ)],
      Same.set _ _ _,
      Cst.of_fr hc (Fr.set a _ (by simp : vJ ∈ [acceptanceTotal, vJ])) (by decide),
      Fr.set a _ (by simp)⟩

def addSample : St VV MM :=
  .ite (.eq maskFlag v1) (.seq (.op (.inc maskTotal)) addAcceptance) skipS

def totalsScratch : List (Fin VV) := [maskTotal, acceptanceTotal, vJ]

theorem addSample_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (pred mask : Bool) (hp : a.env predicateFlag = pred.toNat)
    (hm : a.env maskFlag = mask.toNat)
    (hA : a.env acceptanceTotal + 1 < 2 ^ C.Wd)
    (hM : a.env maskTotal + 1 < 2 ^ C.Wd) :
    Hs C addSample a 5 (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal + (pred && mask).toNat ∧
      b.env maskTotal = a.env maskTotal + mask.toNat ∧
      Same a b ∧ Cst b ∧ Fr a b totalsScratch) := by
  refine Hs.ite (c := .eq maskFlag v1) (t := 4) (show maskFlag ≠ v1 by decide) ?_ ?_
  · intro he
    have ht : mask = true := by
      revert he
      simp only [Cnd.eval, hm, hc.one]
      cases mask <;> simp
    refine Hs.seq (t1 := 1) (t2 := 2) (hs_inc C maskTotal a hM) ?_
    rintro b rfl
    have hfr : Fr a (a.set maskTotal (a.env maskTotal + 1)) totalsScratch :=
      Fr.set a _ (by simp [totalsScratch])
    have hbc := Cst.of_fr hc hfr (by decide)
    refine (addAcceptance_run C _ hbc pred
      ((hfr _ (by decide)).trans hp) (by rw [DS.set_env_ne _ _ (by decide : acceptanceTotal ≠ maskTotal)]; exact hA)).mono le_rfl ?_
    intro d ⟨hd, hsame, hdc, hdfr⟩
    refine ⟨?_, ?_, (Same.set _ _ _).trans hsame, hdc,
      hfr.trans (hdfr.weaken (by simp [totalsScratch]))⟩
    · simpa [ht, DS.set_env_ne _ _ (by decide : acceptanceTotal ≠ maskTotal)] using hd
    · rw [hdfr maskTotal (by decide)]
      simp [ht]
  · intro he
    have ht : mask = false := by
      revert he
      simp only [Cnd.eval, hm, hc.one]
      cases mask <;> simp
    refine (skip_spec a).mono (by omega) ?_
    rintro b rfl
    exact ⟨by simp [ht, DS.set_env_ne _ _ (by decide : acceptanceTotal ≠ vJ)],
      by simp [ht, DS.set_env_ne _ _ (by decide : maskTotal ≠ vJ)], Same.set _ _ _,
      Cst.of_fr hc (Fr.set a _ (by simp [totalsScratch] : vJ ∈ totalsScratch)) (by decide),
      Fr.set a _ (by simp [totalsScratch])⟩

end NearQuarticWires.StageMain.Controller
