import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# No work or witness reads after a failed public guard

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- Once a guard in `sec:params`, paper/paper.tex, has failed, every remaining stage is skipped. The
execution preserves both cursors and output, with work linear
in the number of remaining public stages. -/
theorem guardedPreparationStages_failed (C : Ctx) (ss : List (St VV))
    (a : DS VV) (hc : Cst a) (hfailed : a.env vADM ≠ 1) :
    Hs C (guardedPreparationStages ss) a (3 * ss.length + 1) (fun b =>
      b.env vADM = a.env vADM ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ Fr a b [vJ]) := by
  induction ss generalizing a with
  | nil =>
    refine Hs.mono (skip_spec a) (by simp) ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)], rfl, rfl, rfl,
      hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
  | cons s ss ih =>
    unfold guardedPreparationStages
    have hskip : Hs C (NearCubicGates.Close.Dispatch.guard s) a 2
        (fun b => b = a.set vJ 0) := by
      unfold NearCubicGates.Close.Dispatch.guard
      refine Hs.ite (show vADM ≠ v1 by decide) ?_ ?_
      · intro he
        have hbad : a.env vADM = 1 := by simpa only [Cnd.eval, hc.one, decide_eq_true_eq] using he
        exact False.elim (hfailed hbad)
      · intro _
        exact Hs.mono (skip_spec a) le_rfl (fun _ h => h)
    refine Hs.mono (Hs.seq (t2 := 3 * ss.length + 1) hskip ?_)
      (by simp only [List.length_cons]; omega) (fun _ h => h)
    rintro b rfl
    have hcb : Cst (a.set vJ 0) := hc.set _ _ (by decide)
    have hbfailed : (a.set vJ 0).env vADM ≠ 1 := by
      rw [DS.set_env_ne _ _ (by decide)]
      exact hfailed
    refine Hs.mono (ih (a.set vJ 0) hcb hbfailed) le_rfl ?_
    rintro d ⟨hdadm, hdcp, hdwq, hdout, hdc, hdfr⟩
    exact ⟨by rw [hdadm, DS.set_env_ne _ _ (by decide)], hdcp, hdwq, hdout, hdc,
      Fr.trans (Fr.set _ _ (by decide)) hdfr⟩

end NearQuarticWires.StagePrep
