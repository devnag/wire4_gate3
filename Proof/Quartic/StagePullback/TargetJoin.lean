import Proof.Quartic.StagePullback.SignedTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.SignedCoefficients

open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms

/-- `imp:pullback`, paper/paper.tex: canonical signed
encoding of the exact difference of the two affine target accumulators. -/
theorem difference_encoding (p n : ℕ) :
    SInt.encS ((p : ℤ) - n) =
      if p < n then 2 * (n - p) + 1 else 2 * (p - n) := by
  by_cases h : p < n
  · have ha : ((p : ℤ) - n).natAbs = n - p := by
      rw [show (p : ℤ) - n = -((n : ℤ) - p) by ring, Int.natAbs_neg,
        Int.natAbs_sub_of_nonneg_of_le (by omega) (by omega)]
      simp
    simp only [SInt.encS, ha, if_pos h, if_pos (show (p : ℤ) - n < 0 by omega)]
  · have ha : ((p : ℤ) - n).natAbs = p - n := by
      rw [Int.natAbs_sub_of_nonneg_of_le (by omega) (by omega)]
      simp
    simp only [SInt.encS, ha, if_neg h, if_neg (show ¬ (p : ℤ) - n < 0 by omega), Nat.add_zero]

/-- `imp:pullback`, paper/paper.tex: physically
compare and subtract the two affine accumulators, then write the correct
canonical sign-magnitude field, with sign zero at equality. -/
def targetProgram : St VV MM :=
  .ite (.lt positive negative)
    (.seq (.op (.copy value negative)) (.seq (.op (.sub value positive))
      (.seq (.op (.shl value)) (.op (.inc value)))))
    (.seq (.op (.copy value positive)) (.seq (.op (.sub value negative)) (.op (.shl value))))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: final signed target cancellation is implemented by paid
binary comparison, subtraction and encoding operations. -/
theorem targetProgram_run (C : Ctx) (a : DS VV MM)
    (hfit : 2 * (a.env positive + a.env negative) + 1 < 2 ^ C.Wd) :
    Hs C targetProgram a 8 (fun b =>
      b.env value = SInt.encS ((a.env positive : ℤ) - a.env negative) ∧
      b.sh = a.sh ∧ Fr a b [value]) := by
  unfold targetProgram
  by_cases hn : a.env positive < a.env negative
  · refine Hs.iteT (show positive ≠ negative by decide) (by simp [Cnd.eval, hn]) ?_
    refine Hx.hs (Hs.then (hs_copy C value negative a (by decide))
      (fun b hb n1 hn1 => ?_))
    subst hb
    refine Hs.then (hs_sub C value positive _ (by decide)
      (by vsimp []; omega)) (fun b hb n2 hn2 => ?_)
    subst hb
    refine Hs.then (hs_shl C value _ (by vsimp []; omega)) (fun b hb n3 hn3 => ?_)
    subst hb
    refine Hs.last (hs_inc C value _ (by vsimp []; omega)) ?_
    rintro b hb n4 hn4
    subst hb
    refine ⟨⟨?_, rfl, ?_⟩, by omega⟩
    · rw [difference_encoding, if_pos hn]
      vsimp []
    · exact (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))
  · refine Hs.iteF (t := 7) (show positive ≠ negative by decide)
      (by simp [Cnd.eval, hn]) ?_
    refine Hx.hs (Hs.then (hs_copy C value positive a (by decide))
      (fun b hb n1 hn1 => ?_))
    subst hb
    refine Hs.then (hs_sub C value negative _ (by decide)
      (by vsimp []; omega)) (fun b hb n2 hn2 => ?_)
    subst hb
    refine Hs.last (hs_shl C value _ (by vsimp []; omega)) ?_
    rintro b hb n3 hn3
    subst hb
    refine ⟨⟨?_, rfl, ?_⟩, by omega⟩
    · rw [difference_encoding, if_neg hn]
      vsimp []
    · exact (Fr.set a _ (by simp)).trans
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

end NearQuarticWires.StagePullback.SignedCoefficients
