import Proof.Gates.Dispatch.Arith2
import Proof.Quartic.Cells.ParametersArithmetic

/-!
# The exact integer square-root ceiling

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The integer-power square-root ceiling of `sec:params`,
paper/paper.tex. -/
def ceilSqrtProgram : St VV :=
  .seq sqrtv (.seq (.op (.copy SQU SQS))
    (.seq (.op (.mul SQS SQU SQT))
      (.ite (.eq SQT SQX) skipS (.op (.inc SQS)))))

/-- The program for `sec:params`, paper/paper.tex,
computes the canonical integer square-root ceiling exactly. -/
theorem ceilSqrtProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (x : ℕ) (hx : a.env SQX = x)
    (hW : x * x + x + 3 < 2 ^ C.Wd) :
    Hs C ceilSqrtProgram a (20 * x + 60) (fun b =>
      b.env SQS = Cells.ParameterArithmetic.ceilSqrt x ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [SQS, SQF, SQT, SQU, vJ]) := by
  have hroot : Nat.sqrt x ≤ x := Nat.sqrt_le_self x
  unfold ceilSqrtProgram
  refine Hx.hs (Hs.then (sqrtv_spec a hc x hx (by omega))
    (fun b ⟨hbs, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C SQU SQS b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  have hmul : (b.set SQU (b.env SQS)).env SQS *
      (b.set SQU (b.env SQS)).env SQU < 2 ^ C.Wd := by
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hbs]
    have hsquare := Nat.mul_le_mul hroot hroot
    omega
  refine Hs.then (hs_mul C SQS SQU SQT _ (by decide) (by decide) (by decide) hmul)
    (fun e he n3 hn3 => ?_)
  subst he
  let d := (b.set SQU (b.env SQS)).set SQT
    ((b.set SQU (b.env SQS)).env SQS * (b.set SQU (b.env SQS)).env SQU)
  have hds : d.env SQS = Nat.sqrt x := by
    simp only [d]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hbs]
  have hdq : d.env SQT = (Nat.sqrt x) ^ 2 := by
    simp only [d]
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), DS.set_env_self, hbs, pow_two]
  have hdx : d.env SQX = x := by
    simp only [d]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hbfr _ (by decide), hx]
  have hdc : Cst d := (hbc.set SQU _ (by decide)).set SQT _ (by decide)
  have hdfr : Fr a d [SQS, SQF, SQT, SQU, vJ] :=
    Fr.trans hbfr (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
  have hbranch : Hs C (.ite (.eq SQT SQX) skipS (.op (.inc SQS))) d 2 (fun f =>
      f.env SQS = Cells.ParameterArithmetic.ceilSqrt x ∧
      f.cp = d.cp ∧ f.wq = d.wq ∧ f.out = d.out ∧ Cst f ∧
      Fr d f [SQS, SQF, SQT, SQU, vJ]) := by
    refine Hs.ite (c := .eq SQT SQX) (show SQT ≠ SQX by decide) ?_ ?_
    · intro heq
      have hsq : (Nat.sqrt x) ^ 2 = x := by simpa only [Cnd.eval, hdq, hdx, decide_eq_true_eq] using heq
      refine Hs.mono (skip_spec d) le_rfl ?_
      rintro f rfl
      refine ⟨?_, rfl, rfl, rfl, hdc.set vJ _ (by decide), Fr.set _ _ (by decide)⟩
      rw [DS.set_env_ne _ _ (by decide), hds]
      simp only [Cells.ParameterArithmetic.ceilSqrt, hsq, if_true]
    · intro heq
      have hsq : (Nat.sqrt x) ^ 2 ≠ x := by simpa only [Cnd.eval, hdq, hdx, decide_eq_false_iff_not] using heq
      refine Hs.mono (hs_inc C SQS d (by rw [hds]; omega)) le_rfl ?_
      rintro f rfl
      refine ⟨?_, rfl, rfl, rfl, hdc.set SQS _ (by decide), Fr.set _ _ (by decide)⟩
      rw [DS.set_env_self, hds]
      simp only [Cells.ParameterArithmetic.ceilSqrt, hsq, if_false]
  refine Hs.last hbranch (fun f ⟨hfs, hfcp, hfwq, hfout, hfc, hffr⟩ n4 hn4 => ?_)
  exact ⟨⟨hfs, hfcp.trans hbcp, hfwq.trans hbwq, hfout.trans hbout, hfc,
    Fr.trans hdfr hffr⟩, by omega⟩

end NearQuarticWires.StagePrep
