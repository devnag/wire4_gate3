import Proof.Gates.Dispatch.Arith2

/-!
# Maximum comparisons in the public parameter rules

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The maximum operation in `sec:params`, paper/paper.tex, uses one copy and one integer comparison. -/
def maxRegister (z x y : Fin VV) : St VV :=
  .seq (.op (.copy z x)) (.ite (.lt z y) (.op (.copy z y)) skipS)

/-- The maximum operation of `sec:params`, paper/paper.tex, is exact in four language steps. -/
theorem maxRegister_spec (C : Ctx) (z x y : Fin VV)
    (hzx : z ≠ x) (hzy : z ≠ y) (hzj : z ≠ vJ)
    (hzsafe : z ∉ [vZ, v1, v2, vPOS]) (a : DS VV) (hc : Cst a) :
    Hs C (maxRegister z x y) a 4 (fun b =>
      b.env z = max (a.env x) (a.env y) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [z, vJ]) := by
  unfold maxRegister
  refine Hs.seq (t2 := 2) (hs_copy C z x a hzx) ?_
  rintro d rfl
  refine Hs.ite (c := .lt z y) hzy ?_ ?_
  · intro hlt
    have hxy : a.env x < a.env y := by
      simpa only [Cnd.eval, DS.set_env_self, DS.set_env_ne _ _ hzy.symm,
        decide_eq_true_eq] using hlt
    refine Hs.mono (hs_copy C z y _ hzy) le_rfl ?_
    rintro b rfl
    refine ⟨?_, rfl, rfl, rfl, (hc.set z _ hzsafe).set z _ hzsafe, ?_⟩
    · rw [DS.set_env_self, DS.set_env_ne _ _ hzy.symm, max_eq_right hxy.le]
    · exact Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp))
  · intro hlt
    have hyx : a.env y ≤ a.env x := by
      simp only [Cnd.eval, DS.set_env_self, DS.set_env_ne _ _ hzy.symm,
        decide_eq_false_iff_not] at hlt
      omega
    refine Hs.mono (skip_spec _) le_rfl ?_
    rintro b rfl
    refine ⟨?_, rfl, rfl, rfl, (hc.set z _ hzsafe).set vJ _ (by decide), ?_⟩
    · rw [DS.set_env_ne _ _ hzj, DS.set_env_self, max_eq_left hyx]
    · exact Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp))

end NearQuarticWires.StagePrep
