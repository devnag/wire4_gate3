import Proof.Quartic.StageCert.DigitCoefficient

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `eq:testE`, `eq:testPhi` and `lem:print`, paper/paper.tex: exact sign and magnitude are obtained by
ordered natural subtraction, including cancellation to zero. -/
def normalizeLinearCoefficient : St VV MM :=
  .ite (.lt linearPositive linearNegative)
    (.seq (.op (.copy newtonMagnitudeField linearNegative))
      (.seq (.op (.sub newtonMagnitudeField linearPositive))
        (.op (.copy newtonSignField v1))))
    (.seq (.op (.copy newtonMagnitudeField linearPositive))
      (.seq (.op (.sub newtonMagnitudeField linearNegative))
        (.op (.zero newtonSignField))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact original integer coefficient is normalized
in six operations, with no division, residue or semantic premise. -/
theorem normalizeLinearCoefficient_run (C : Ctx) (positive negative : ℕ)
    (a : DS VV MM) (hc : Cst a) (hp : a.env linearPositive=positive)
    (hn : a.env linearNegative=negative) :
    Hs C normalizeLinearCoefficient a 6 (fun z=>
      z.env newtonSignField=(if (positive:ℤ)-negative<0 then 1 else 0) ∧
      z.env newtonMagnitudeField=((positive:ℤ)-negative).natAbs ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [newtonSignField,newtonMagnitudeField]) := by
  unfold normalizeLinearCoefficient
  refine Hs.ite (t := 5) (c := .lt linearPositive linearNegative)
    (show linearPositive≠linearNegative by decide) ?_ ?_
  · intro he
    have hl : positive<negative := by simpa only [Cnd.eval,hp,hn,decide_eq_true_eq] using he
    refine Hs.seq (t1 := 1) (t2 := 3)
      (hs_copy C newtonMagnitudeField linearNegative a (by decide)) ?_
    rintro b rfl
    refine Hs.seq (t1 := 1) (t2 := 1)
      (hs_sub C newtonMagnitudeField linearPositive _ (by decide)
        (by vsimp [hp,hn]; omega)) ?_
    rintro d rfl
    refine (hs_copy C newtonSignField v1 _ (by decide)).mono le_rfl ?_
    rintro z rfl
    refine ⟨?_,?_,rfl,?_,
      (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩
    · rw [if_pos (by omega)]
      vsimp [hc.one]
    · rw [Int.natAbs_natCast_sub_natCast_of_le hl.le]
      vsimp [hp,hn]
    · exact Cst.of_fr (T := [newtonSignField,newtonMagnitudeField]) hc
        ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))) (by decide)
  · intro he
    have hl : negative≤positive := by
      simpa only [Cnd.eval,hp,hn,decide_eq_false_iff_not,not_lt] using he
    refine Hs.seq (t1 := 1) (t2 := 3)
      (hs_copy C newtonMagnitudeField linearPositive a (by decide)) ?_
    rintro b rfl
    refine Hs.seq (t1 := 1) (t2 := 1)
      (hs_sub C newtonMagnitudeField linearNegative _ (by decide)
        (by vsimp [hp,hn]; omega)) ?_
    rintro d rfl
    refine (hs_zero C newtonSignField _).mono le_rfl ?_
    rintro z rfl
    refine ⟨?_,?_,rfl,?_,
      (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩
    · rw [if_neg (by omega)]
      rfl
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hl]
      vsimp [hp,hn]
    · exact Cst.of_fr (T := [newtonSignField,newtonMagnitudeField]) hc
        ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))) (by decide)

end NearQuarticWires.StageCert.Tokens
