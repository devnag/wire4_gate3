import Proof.Quartic.StagePrep.FailedStages

/-!
# Execution through an active public guard

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- An active guard in `sec:params`, paper/paper.tex, executes its actual instruction sequence, charging
the comparison in addition to the complete body execution. -/
theorem activeGuard_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (s : St VV) (t : ℕ) (R : DS VV → Prop) (ha : a.env vADM=1)
    (h : Hs C s a t R) :
    Hs C (NearCubicGates.Close.Dispatch.guard s) a (t+2) R := by
  unfold NearCubicGates.Close.Dispatch.guard
  refine Hs.ite (show vADM≠v1 by decide) (fun _ => Hs.mono h (by omega) (fun _ h => h)) ?_
  intro hbad
  simp only [Cnd.eval,ha,hc.one,decide_true] at hbad
  cases hbad

end NearQuarticWires.StagePrep
