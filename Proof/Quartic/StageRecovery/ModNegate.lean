import Proof.Quartic.StageRecovery.ModArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: negation of a reduced
residue uses subtraction from the actual modulus followed by division. -/
def negateModProgram (argument : Fin VV) : St VV MM :=
  .seq (.op (.copy productVar modulusVar))
    (.seq (.op (.sub productVar argument))
      (.seq (.op (.dm productVar modulusVar quotientVar remainderVar))
        (.op (.copy argument remainderVar))))

/-- `lem:print`, paper/paper.tex: the actual modular
negation computes the normalized residue of the additive inverse,
including the zero input, with unchanged source and output cursors. -/
theorem negateModProgram_spec (C : Ctx) (a : DS VV MM) (argument : Fin VV)
    (harg : argument ≠ productVar ∧ argument ≠ modulusVar ∧
      argument ≠ quotientVar ∧ argument ≠ remainderVar)
    (hq : 0 < a.env modulusVar) (hqfit : 2 * a.env modulusVar ≤ 2 ^ C.Wd)
    (hvalue : a.env argument ≤ a.env modulusVar) :
    Hs C (negateModProgram argument) a 7 (fun b =>
      b.env argument = (a.env modulusVar - a.env argument) % a.env modulusVar ∧
      b.sh = a.sh ∧ Fr a b [argument, productVar, quotientVar, remainderVar]) := by
  unfold negateModProgram
  refine Hs.seq (t2 := 5) (hs_copy C productVar modulusVar a (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 3) (hs_sub C productVar argument _ (Ne.symm harg.1)
    (by simpa only [DS.set_env_self, DS.set_env_ne _ _ harg.1] using hvalue)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_dm C productVar modulusVar quotientVar remainderVar _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa (config := {decide := true}) [DS.set] using hq)
    (by simpa (config := {decide := true}) [DS.set] using hqfit)) fun b hb => ?_
  subst b
  refine (hs_copy C argument remainderVar _ harg.2.2.2).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_, rfl, ?_⟩
  · simp only [DS.set_env_self, DS.set_env_ne _ _ harg.1,
      DS.set_env_ne _ _ (show modulusVar ≠ productVar by decide)]
  · exact Fr.trans (Fr.set _ _ (by simp))
      (Fr.trans (Fr.set _ _ (by simp))
        (Fr.trans (Fr.set _ _ (by simp))
          (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp)))))

end NearQuarticWires.StageRecovery
