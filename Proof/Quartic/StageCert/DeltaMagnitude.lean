import Proof.Quartic.StageCert.DeltaCounts

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch

/-- `def:mask`, paper/paper.tex: exact integer absolute
value is computed by an ordered natural subtraction, retaining its sign counts. -/
def absoluteDelta : St VV := .ite (.lt deltaPositive deltaNegative)
  (.seq (.op (.copy deltaMagnitude deltaNegative)) (.op (.sub deltaMagnitude deltaPositive)))
  (.seq (.op (.copy deltaMagnitude deltaPositive)) (.op (.sub deltaMagnitude deltaNegative)))

/-- `def:mask`, paper/paper.tex: the physical magnitude
is the exact natural absolute value of the signed mixed difference. -/
theorem absoluteDelta_run (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C absoluteDelta a 4 (fun z =>
      z.env deltaMagnitude=((a.env deltaPositive : ℤ)-(a.env deltaNegative : ℤ)).natAbs ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z [deltaMagnitude]) := by
  unfold absoluteDelta
  refine Hs.ite (c := .lt deltaPositive deltaNegative) (show deltaPositive≠deltaNegative by decide) ?_ ?_
  · intro he
    have hl : a.env deltaPositive<a.env deltaNegative := by
      simpa only [Cnd.eval,decide_eq_true_eq] using he
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C deltaMagnitude deltaNegative a (by decide)) ?_
    rintro b rfl
    refine (hs_sub C deltaMagnitude deltaPositive _ (by decide)
      (by vsimp [deltaMagnitude,deltaPositive,deltaNegative]; exact hl.le)).mono le_rfl ?_
    rintro z rfl
    refine ⟨?_,rfl,rfl,rfl,?_,(Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
    · rw [Int.natAbs_natCast_sub_natCast_of_le hl.le]
      vsimp [deltaMagnitude,deltaPositive,deltaNegative]
    · exact ⟨by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.z],
        by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.one],
        by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.two],
        by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.pos]⟩
  · intro he
    have hl : a.env deltaNegative≤a.env deltaPositive := by
      simpa only [Cnd.eval,decide_eq_false_iff_not,not_lt] using he
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C deltaMagnitude deltaPositive a (by decide)) ?_
    rintro b rfl
    refine (hs_sub C deltaMagnitude deltaNegative _ (by decide)
      (by vsimp [deltaMagnitude,deltaPositive,deltaNegative]; exact hl)).mono le_rfl ?_
    rintro z rfl
    refine ⟨?_,rfl,rfl,rfl,?_,(Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hl]
      vsimp [deltaMagnitude,deltaPositive,deltaNegative]
    · exact ⟨by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.z],
        by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.one],
        by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.two],
        by vsimp [deltaMagnitude,deltaPositive,deltaNegative,hc.pos]⟩

end NearQuarticWires.StageCert
