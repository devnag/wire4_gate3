import Proof.Quartic.StagePullback.TargetJoin

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.SignedCoefficients

open NearCubicGates.Close.Cells

/-- `imp:pullback`, paper/paper.tex: insert the
original target into the positive and negative affine accumulators. -/
theorem inserted_difference (p n : ℕ) (z : ℤ) :
    ((p + (if z < 0 then 0 else z.natAbs) : ℕ) : ℤ) -
      ((n + (if z < 0 then z.natAbs else 0) : ℕ) : ℤ) = (p : ℤ) - n + z := by
  by_cases hz : z < 0
  · simp only [hz, if_true, Nat.add_zero, Nat.cast_add, Int.natCast_natAbs, abs_of_neg hz]
    ring
  · simp only [hz, if_false, Nat.add_zero, Nat.cast_add, Int.natCast_natAbs,
      abs_of_nonneg (by omega : 0 ≤ z)]
    ring

/-- `imp:pullback`, paper/paper.tex: one actual
binary addition inserts the original signed target without altering any
coefficient already stored in the native halves. -/
def insertTargetProgram : St VV MM :=
  .ite (.eq sign vZ) (.op (.add positive magnitude)) (.op (.add negative magnitude))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the original target is inserted with exact signed
semantics and exact absolute mass, paying for the binary operation. -/
theorem insertTargetProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ)
    (hm : a.env magnitude = z.natAbs) (hs : a.env sign = if z < 0 then 1 else 0)
    (hpfit : a.env positive + z.natAbs < 2 ^ C.Wd)
    (hnfit : a.env negative + z.natAbs < 2 ^ C.Wd) :
    Hs C insertTargetProgram a 2 (fun b =>
      (b.env positive : ℤ) - b.env negative = (a.env positive : ℤ) - a.env negative + z ∧
      b.env positive + b.env negative = a.env positive + a.env negative + z.natAbs ∧
      b.sh = a.sh ∧ Fr a b [positive, negative]) := by
  unfold insertTargetProgram
  by_cases hz : z < 0
  · refine Hs.mono (Hs.iteF (show sign ≠ vZ by decide)
      (by simp [Cnd.eval, hs, hz, hc.z])
      (hs_add C negative magnitude a (by decide) (by rw [hm]; exact hnfit))) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, rfl, Fr.set a _ (by simp)⟩
    · simpa only [DS.set_env_self, DS.set_env_ne _ _ (by decide : positive ≠ negative),
        hm, hz, if_true, Nat.add_zero] using inserted_difference (a.env positive) (a.env negative) z
    · rw [DS.set_env_self, DS.set_env_ne _ _ (by decide : positive ≠ negative), hm]
      omega
  · refine Hs.mono (Hs.iteT (show sign ≠ vZ by decide)
      (by simp [Cnd.eval, hs, hz, hc.z])
      (hs_add C positive magnitude a (by decide) (by rw [hm]; exact hpfit))) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, rfl, Fr.set a _ (by simp)⟩
    · simpa only [DS.set_env_self, DS.set_env_ne _ _ (by decide : negative ≠ positive),
        hm, hz, if_false, Nat.add_zero] using inserted_difference (a.env positive) (a.env negative) z
    · rw [DS.set_env_self, DS.set_env_ne _ _ (by decide : negative ≠ positive), hm]
      omega

end NearQuarticWires.StagePullback.SignedCoefficients
