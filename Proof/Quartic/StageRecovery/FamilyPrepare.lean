import Proof.Quartic.StageRecovery.FamilySetup

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: native family setup
computes its width, original support radix and mask by actual arithmetic. -/
def prepareFamilyProgram : St VV MM :=
  .seq familyWidthProgram (.seq familyRadixProgram familyMaskProgram)

/-- `lem:print`, paper/paper.tex: all finite setup
work words are separate from the original Formula header fields. -/
def familyPrepareScratch : List (Fin VV) :=
  [FixedBits.width, coordinateBaseVar, familyMaskVar, a1, c4, vJ]

/-- `lem:print`, paper/paper.tex: one actual setup
program constructs every numeric native field from the decoded original
arity and degree, without supplied binary work tapes. -/
theorem prepareFamilyProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (r : FamilyRequest) (hV : a.env arityVar = r.arity) (hD : a.env familyBoundVar = r.degree)
    (hwidth : r.arity + r.degree + 10 ≤ C.Wd) :
    Hs C prepareFamilyProgram a (7 * r.arity + 34) (fun b =>
      b.env FixedBits.width = r.width ∧ b.env coordinateBaseVar = 2 ^ r.arity ∧
      b.env familyMaskVar = 2 ^ r.arity - 1 ∧ b.sh = a.sh ∧ Cst b ∧ Fr a b familyPrepareScratch) := by
  have hfit : r.arity + r.degree + 8 < 2 ^ C.Wd :=
    lt_of_lt_of_le (by omega) Nat.lt_two_pow_self.le
  unfold prepareFamilyProgram
  refine (Hs.seq (t2 := (7 * r.arity + 8) + 3 + 1)
    (familyWidthProgram_spec C a hc r.arity r.degree hV hD hfit)
    fun b ⟨hbw, hbsh, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  refine Hs.seq (t2 := 3) (familyRadixProgram_spec C b hbc r.arity
    (by rw [hbf _ (by decide), hV]) (by omega)) fun d ⟨hdb, hdsh, hdc, hdf⟩ => ?_
  refine (familyMaskProgram_spec C d hdc r.arity hdb).mono le_rfl ?_
  rintro e ⟨hem, hesh, hec, hef⟩
  exact ⟨by rw [hef _ (by decide), hdf _ (by decide), hbw]; rfl,
    by rw [hef _ (by decide), hdb], hem, hesh.trans (hdsh.trans hbsh), hec,
    Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))⟩

end NearQuarticWires.StageRecovery
