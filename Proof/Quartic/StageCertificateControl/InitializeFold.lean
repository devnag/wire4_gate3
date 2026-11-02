import Proof.Quartic.StageCertificateControl.AlternatingTest
import Proof.Quartic.StageCertTests.FlagInitialize

/-!
# Initialize the two retained full-size bitmap arrays

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicGates.Close.Cells
open StageRecovery (countVar)

/-- The complete conjunction arrays of `sec:algorithm`,
paper/paper.tex, are physically initialized once. -/
def initializeFold (first second : Fin MM) : St VV MM :=
  .seq (StageCertTests.initializeFlags first)
    (.seq (StageCertTests.initializeFlags second) (.op (.zero modeVar)))

/-- Initialization in `sec:algorithm` and `prop:time`,
paper/paper.tex, constructs both
full-size true arrays from empty stores and preserves all original data. -/
theorem initializeFold_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (first second : Fin MM) (hstores : first≠second) (count : ℕ)
    (hn : a.env countVar=count) (hnfit : count<2^C.Wd)
    (hfirst : a.ram first=[]) (hsecond : a.ram second=[])
    (hri : a.rc first=0) (hro : a.rc second=0) :
    Hs C (initializeFold first second) a (10*count+11) (fun b =>
      b.env modeVar=0 ∧
      b.ram=Function.update (Function.update a.ram first (List.replicate count 1))
        second (List.replicate count 1) ∧
      b.rc=Function.update (Function.update a.rc first count) second count ∧
      (b.ip,b.out,b.kin,b.kout,b.kc)=(a.ip,a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [c0,modeVar]) := by
  unfold initializeFold
  refine (Hs.seq (t2 := 5*count+6)
    (StageCertTests.initializeFlags_spec C a hc first count hn hnfit hfirst hri)
    fun b ⟨hba,hbra,hbs,hbo,hbc,hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbsecond : b.ram second=[] := (hbo second (Ne.symm hstores)).1.trans hsecond
  have hbrsecond : b.rc second=0 := (hbo second (Ne.symm hstores)).2.trans hro
  refine Hs.seq (t2 := 1)
    (StageCertTests.initializeFlags_spec C b hbc second count
      ((hbf _ (by decide)).trans hn) hnfit hbsecond hbrsecond)
    fun d ⟨hdb,hdrb,hds,hdo,hdc,hdf⟩ => ?_
  refine (hs_zero C modeVar d).mono le_rfl ?_
  rintro e rfl
  refine ⟨by simp,?_,?_,hds.trans hbs,?_,?_⟩
  · change d.ram=_
    funext store
    by_cases hs2 : store=second
    · subst store
      simp only [Function.update_self]
      exact hdb
    · by_cases hs1 : store=first
      · subst store
        simp only [Function.update_of_ne hstores,Function.update_self]
        exact (hdo first hstores).1.trans hba
      · simp only [Function.update_of_ne hs2,Function.update_of_ne hs1]
        exact (hdo store hs2).1.trans (hbo store hs1).1
  · change d.rc=_
    funext store
    by_cases hs2 : store=second
    · subst store
      simp only [Function.update_self]
      exact hdrb
    · by_cases hs1 : store=first
      · subst store
        simp only [Function.update_of_ne hstores,Function.update_self]
        exact (hdo first hstores).2.trans hbra
      · simp only [Function.update_of_ne hs2,Function.update_of_ne hs1]
        exact (hdo store hs2).2.trans (hbo store hs1).2
  · exact Cst.of_fr (T := [modeVar]) hdc (Fr.set _ _ (by decide)) (by decide)
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide)) (Fr.set _ _ (by decide)))

end NearQuarticWires.StageCertificateControl
