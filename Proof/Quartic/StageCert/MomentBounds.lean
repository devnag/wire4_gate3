import Proof.Quartic.StageCert.Records

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open Finset

/-- `lem:maskpoly`, paper/paper.tex: the Newton polynomial
has an explicit magnitude bound even outside the certified population range. -/
theorem maskPolyEval_abs_le (s : Bool) (tau Xmax X : ℕ) :
    |Mask.maskPolyEval s tau Xmax X| ≤ (Xmax+1 : ℕ)*(2 : ℤ)^(Xmax+X) := by
  cases s with
  | false => simp [Mask.maskPolyEval]
  | true =>
    simp only [Mask.maskPolyEval, ↓reduceIte, one_mul]
    calc
      |∑ a ∈ range (Xmax+1), Mask.newtonCoeff tau a*(X.choose a : ℤ)| ≤
          ∑ a ∈ range (Xmax+1), |Mask.newtonCoeff tau a*(X.choose a : ℤ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ range (Xmax+1), (2 : ℤ)^Xmax*2^X := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' : a ≤ Xmax := by simpa using ha
        have hc := Mask.newtonCoeff_abs_le tau a
        have hp : (2 : ℤ)^a ≤ 2^Xmax := pow_le_pow_right₀ (by norm_num) ha'
        have hb : (X.choose a : ℤ) ≤ 2^X := by exact_mod_cast Nat.choose_le_two_pow X a
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
        exact mul_le_mul (hc.trans hp) hb (Int.natCast_nonneg _) (by positivity)
      _ = _ := by simp [pow_add]

/-- `lem:maskpoly` and `eq:testE`, paper/paper.tex: all eight edge factors have polynomially bounded bit height before
any certification test has passed. -/
theorem walkMaskPoly_abs_le {N : ℕ} (s : NearQuarticWires.Sampler.Cell N → Bool)
    (tau Xmax G : ℕ) (X : NearQuarticWires.Sampler.Cell N → ℕ)
    (hX : ∀ c, X c ≤ G) (w : Cycle.Walk N 4) :
    |Walks.walkMaskPoly (by norm_num) s tau Xmax X w| ≤
      ((Xmax+1 : ℕ)*(2 : ℤ)^(Xmax+G))^8 := by
  unfold Walks.walkMaskPoly
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _l : Fin 8, ((Xmax+1 : ℕ)*(2 : ℤ)^(Xmax+G)) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro l _
      refine (maskPolyEval_abs_le _ tau Xmax _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_left (hX _) _)
    _ = _ := by simp

/-- `eq:testE`–`eq:testPhi`, paper/paper.tex: a complete
signed masked moment is bounded by its actual finite cardinality and the
scalar ranges, without assuming the mask is already Boolean. -/
theorem maskedMoment_abs_le {V : Type*} [Fintype V] (K M B : ℕ) (mask value : V → ℤ)
    (hm : ∀ x, |mask x| ≤ M) (hv : ∀ x, |value x| ≤ B) :
    |Walks.maskedMoment K mask value| ≤ (Fintype.card V : ℤ)*M*(B : ℤ)^(2*K) := by
  classical
  unfold Walks.maskedMoment
  calc
    |∑ x, mask x*value x^(2*K)| ≤ ∑ x, |mask x*value x^(2*K)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : V, (M : ℤ)*(B : ℤ)^(2*K) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hm x) (pow_le_pow_left₀ (abs_nonneg _) (hv x) _)
        (by positivity) (Int.natCast_nonneg _)
    _ = _ := by simp [mul_assoc]

end NearQuarticWires.StageCert
