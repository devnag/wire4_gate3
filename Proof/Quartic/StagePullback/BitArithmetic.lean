import Proof.Quartic.StagePullback.RightError

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicGates.Close.Cells

/-- `imp:pullback`, paper/paper.tex: xor one
physically decoded marker bit into the retained coordinate bit. -/
def xorInto (x y : Fin VV) : St VV MM :=
  .ite (.eq y v1)
    (.ite (.eq x v1) (.op (.zero x)) (.op (.copy x v1))) skipS

/-- `imp:pullback` and `prop:time`, paper/paper.tex: coordinate xor uses three actual source operations,
preserves the input/output cursors, and changes only its accumulator. -/
theorem xorInto_run (C : Ctx) (x y : Fin VV) (hx : x ≠ v1) (hxj : x ≠ vJ) (hy : y ≠ v1)
    (a : DS VV MM) (hc : Cst a) (u v : Bool)
    (hu : a.env x = u.toNat) (hv : a.env y = v.toNat) :
    Hs C (xorInto x y) a 3 (fun b =>
      b.env x = (xor u v).toNat ∧ b.sh = a.sh ∧ Fr a b [x, vJ]) := by
  unfold xorInto
  cases v with
  | false =>
    refine Hs.mono (Hs.iteF hy (by simp [Cnd.eval, hv, hc.one]) (skip_spec a)) (by omega) ?_
    rintro b rfl
    refine ⟨?_, rfl, Fr.set a _ (by simp)⟩
    rw [DS.set_env_ne _ _ hxj, hu]
    cases u <;> rfl
  | true =>
    refine Hs.iteT hy (by simp [Cnd.eval, hv, hc.one]) ?_
    cases u with
    | false =>
      refine Hs.mono (Hs.iteF hx (by simp [Cnd.eval, hu, hc.one])
        (hs_copy C x v1 a hx)) le_rfl ?_
      rintro b rfl
      exact ⟨by simp [hc.one], rfl, Fr.set a _ (by simp)⟩
    | true =>
      refine Hs.mono (Hs.iteT hx (by simp [Cnd.eval, hu, hc.one])
        (hs_zero C x a)) le_rfl ?_
      rintro b rfl
      exact ⟨by simp, rfl, Fr.set a _ (by simp)⟩

end NearQuarticWires.StagePullback
