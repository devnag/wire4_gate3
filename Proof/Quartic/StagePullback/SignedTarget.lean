import Proof.Quartic.StagePullback.SignedCoefficient

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.SignedCoefficients

open NearCubicGates.Close.Cells

/-- `imp:pullback`, paper/paper.tex: the positive and
negative accumulator update represents subtraction of one original
flipped coefficient, including negative coefficients. -/
theorem shifted_difference (p n : ℕ) (z : ℤ) :
    ((p + (if z < 0 then z.natAbs else 0) : ℕ) : ℤ) -
      ((n + (if z < 0 then 0 else z.natAbs) : ℕ) : ℤ) = (p : ℤ) - n - z := by
  by_cases hz : z < 0
  · simp only [hz, if_true, Nat.add_zero, Nat.cast_add, Int.natCast_natAbs, abs_of_neg hz]
    ring
  · simp only [hz, if_false, Nat.add_zero, Nat.cast_add, Int.natCast_natAbs,
      abs_of_nonneg (by omega : 0 ≤ z)]
    ring

/-- `imp:pullback`, paper/paper.tex: a flipped
positive weight increments the negative correction and a flipped negative
weight increments the positive correction. -/
def shiftProgram : St VV MM :=
  .ite (.eq sign vZ) (.op (.add negative magnitude)) (.op (.add positive magnitude))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the exact affine target correction is computed by one
paid binary addition, with no free sign cancellation. -/
theorem shiftProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ)
    (hm : a.env magnitude = z.natAbs) (hs : a.env sign = if z < 0 then 1 else 0)
    (hpfit : a.env positive + z.natAbs < 2 ^ C.Wd)
    (hnfit : a.env negative + z.natAbs < 2 ^ C.Wd) :
    Hs C shiftProgram a 2 (fun b =>
      b.env positive = a.env positive + (if z < 0 then z.natAbs else 0) ∧
      b.env negative = a.env negative + (if z < 0 then 0 else z.natAbs) ∧
      (b.env positive : ℤ) - b.env negative = (a.env positive : ℤ) - a.env negative - z ∧
      b.sh = a.sh ∧ Fr a b [positive, negative]) := by
  unfold shiftProgram
  by_cases hz : z < 0
  · refine Hs.mono (Hs.iteF (show sign ≠ vZ by decide)
      (by simp [Cnd.eval, hs, hz, hc.z])
      (hs_add C positive magnitude a (by decide) (by rw [hm]; exact hpfit))) le_rfl ?_
    rintro b rfl
    refine ⟨by simp [hm, hz], ?_, ?_, rfl, Fr.set a _ (by simp)⟩
    · rw [DS.set_env_ne _ _ (by decide : negative ≠ positive)]
      simp only [hz, if_true, Nat.add_zero]
    · simpa only [DS.set_env_self, DS.set_env_ne _ _ (by decide : negative ≠ positive),
        hm, hz, if_true, Nat.add_zero] using shifted_difference (a.env positive) (a.env negative) z
  · refine Hs.mono (Hs.iteT (show sign ≠ vZ by decide)
      (by simp [Cnd.eval, hs, hz, hc.z])
      (hs_add C negative magnitude a (by decide) (by rw [hm]; exact hnfit))) le_rfl ?_
    rintro b rfl
    refine ⟨?_, by simp [hm, hz], ?_, rfl, Fr.set a _ (by simp)⟩
    · rw [DS.set_env_ne _ _ (by decide : positive ≠ negative)]
      simp only [hz, if_false, Nat.add_zero]
    · simpa only [DS.set_env_self, DS.set_env_ne _ _ (by decide : positive ≠ negative),
        hm, hz, if_false, Nat.add_zero] using shifted_difference (a.env positive) (a.env negative) z

end NearQuarticWires.StagePullback.SignedCoefficients
