import Proof.Quartic.StageCert.NewtonActive

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: the unit and
vanishing original Newton coefficients have literal constant-result branches. -/
def constantNewton (one : Bool) : St VV MM :=
  .seq (.op (.zero newtonSignField))
    (if one then .op (.copy newtonMagnitudeField v1) else .op (.zero newtonMagnitudeField))

/-- `lem:maskpoly`, paper/paper.tex: a constant
coefficient branch retains every original source field and store. -/
theorem constantNewton_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (one : Bool) :
    Hs C (constantNewton one) a 3 (fun z=>z.env newtonSignField=0 ∧
      z.env newtonMagnitudeField=one.toNat ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [newtonSignField,newtonMagnitudeField]) := by
  cases one
  · unfold constantNewton
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_zero C newtonSignField a) ?_
    rintro b rfl
    refine (hs_zero C newtonMagnitudeField _).mono le_rfl ?_
    rintro z rfl
    refine ⟨by simp [newtonSignField,newtonMagnitudeField],by rfl,rfl,?_,
      (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
    exact ⟨by vsimp [newtonSignField,newtonMagnitudeField,hc.z],
      by vsimp [newtonSignField,newtonMagnitudeField,hc.one],
      by vsimp [newtonSignField,newtonMagnitudeField,hc.two]⟩
  · unfold constantNewton
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_zero C newtonSignField a) ?_
    rintro b rfl
    refine (hs_copy C newtonMagnitudeField v1 _ (by decide)).mono le_rfl ?_
    rintro z rfl
    refine ⟨by simp [newtonSignField,newtonMagnitudeField],?_,rfl,?_,
      (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
    · vsimp [newtonSignField,newtonMagnitudeField,hc.one]
    · exact ⟨by vsimp [newtonSignField,newtonMagnitudeField,hc.z],
        by vsimp [newtonSignField,newtonMagnitudeField,hc.one],
        by vsimp [newtonSignField,newtonMagnitudeField,hc.two]⟩

/-- `lem:maskpoly`, paper/paper.tex: every original
cutoff coefficient is computed from its degree and cutoff by actual binary
branching, multiplication, exact natural division and parity extraction. -/
def computeNewton : St VV MM := .ite (.eq newtonIndex vZ) (constantNewton true)
  (.ite (.lt newtonTau newtonIndex) activeNewton (constantNewton false))

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: all signed original Newton coefficients, including zeros,
are generated with explicit linear operation count and polynomial bit width. -/
theorem computeNewton_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (tau index : ℕ)
    (ht : a.env newtonTau=tau) (hi : a.env newtonIndex=index) (hwidth : 2*index+2≤C.Wd) :
    Hs C computeNewton a (17*index+30) (fun z=>
      z.env newtonSignField=newtonSign tau index ∧
      z.env newtonMagnitudeField=newtonMagnitude tau index ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z newtonScratch) := by
  unfold computeNewton
  refine Hs.ite (t := 17*index+29) (c := .eq newtonIndex vZ)
    (show newtonIndex≠vZ by decide) ?_ ?_
  · intro he
    have hz : index=0 := by simpa only [Cnd.eval,hi,hc.z,decide_eq_true_eq] using he
    refine (constantNewton_run C a hc true).mono (by omega) ?_
    rintro z ⟨zs,zm,zsh,zc,zfr⟩
    exact ⟨by simpa [newtonSign,hz] using zs,by simpa [newtonMagnitude,hz] using zm,
      zsh,zc,zfr.weaken (by decide)⟩
  · intro he
    have hz : index≠0 := by simpa only [Cnd.eval,hi,hc.z,decide_eq_false_iff_not] using he
    refine Hs.ite (t := 17*index+28) (c := .lt newtonTau newtonIndex)
      (show newtonTau≠newtonIndex by decide) ?_ ?_
    · intro hactive
      have hlt : tau < index := by simpa only [Cnd.eval,ht,hi,decide_eq_true_eq] using hactive
      refine (activeNewton_run C a hc tau index ht hi hlt hwidth).mono (by omega) ?_
      rintro z ⟨zm,zs,zsh,zc,zfr⟩
      exact ⟨by simpa [newtonSign,hz,show ¬index≤tau by omega] using zs,
        by simpa [newtonMagnitude,hz,show ¬index≤tau by omega] using zm,zsh,zc,zfr⟩
    · intro hinactive
      have hle : index≤tau := by simpa only [Cnd.eval,ht,hi,decide_eq_false_iff_not,not_lt] using hinactive
      refine (constantNewton_run C a hc false).mono (by omega) ?_
      rintro z ⟨zs,zm,zsh,zc,zfr⟩
      exact ⟨by simpa [newtonSign,hz,hle] using zs,by simpa [newtonMagnitude,hz,hle] using zm,
        zsh,zc,zfr.weaken (by decide)⟩

/-- `lem:maskpoly`, paper/paper.tex: the physical
result fields are exactly the sign and magnitude of the original integer
forward difference, not of a residue or an unsigned surrogate. -/
theorem computeNewton_original (C : Ctx) (a : DS VV MM) (hc : Cst a) (tau index : ℕ)
    (ht : a.env newtonTau=tau) (hi : a.env newtonIndex=index) (hwidth : 2*index+2≤C.Wd) :
    Hs C computeNewton a (17*index+30) (fun z=>
      z.env newtonSignField=(if Mask.newtonCoeff tau index<0 then 1 else 0) ∧
      z.env newtonMagnitudeField=(Mask.newtonCoeff tau index).natAbs ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z newtonScratch) := by
  refine (computeNewton_run C a hc tau index ht hi hwidth).mono le_rfl ?_
  rintro z ⟨zs,zm,zsh,zc,zfr⟩
  exact ⟨zs.trans (newtonFields_exact tau index).1,zm.trans (newtonFields_exact tau index).2,zsh,zc,zfr⟩

end NearQuarticWires.StageCert.Tokens
