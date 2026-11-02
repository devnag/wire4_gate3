import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic

set_option autoImplicit false

namespace NearQuarticWires.Mask

open scoped BigOperators

/-- Paper `def:mask`: the scalar integer value of the Boolean mask. -/
def mask (structural : Bool) (τ X : ℕ) : ℤ :=
  if structural = true ∧ X ≤ τ then 1 else 0

/-- Paper `lem:maskpoly`: the integer cutoff function used by Newton interpolation. -/
def cutoff (τ x : ℕ) : ℤ := if x ≤ τ then 1 else 0

/-- Paper `lem:maskpoly`: the `a`th integer forward difference at zero. -/
def newtonCoeff (τ a : ℕ) : ℤ := ((fwdDiff (1 : ℕ))^[a] (cutoff τ)) 0

/-- Paper `lem:maskpoly`: evaluation of the integer mask polynomial
on Boolean occurrence values, expressed through their population `X`. -/
def maskPolyEval (structural : Bool) (τ Xmax X : ℕ) : ℤ :=
  (if structural then 1 else 0) *
    ∑ a ∈ Finset.range (Xmax + 1), newtonCoeff τ a * (X.choose a : ℤ)

/-- Paper `def:mask`: the mask is an exact integer bit. -/
theorem mask_zero_or_one (structural : Bool) (τ X : ℕ) :
    mask structural τ X = 0 ∨ mask structural τ X = 1 := by
  simp only [mask]
  split_ifs <;> simp

/-- Paper `lem:maskpoly`: Newton's formula for the concrete cutoff. -/
theorem cutoff_eq_newton_sum (τ X : ℕ) :
    cutoff τ X = ∑ a ∈ Finset.range (X + 1), newtonCoeff τ a * (X.choose a : ℤ) := by
  simpa [newtonCoeff, nsmul_eq_mul, mul_comm] using
    (shift_eq_sum_fwdDiff_iter (1 : ℕ) (cutoff τ) X 0)

/-- Paper `lem:maskpoly`: binomial vanishing permits the fixed
upper degree `Xmax`, rather than a population-dependent sum. -/
theorem cutoff_eq_newton_sum_of_le (τ X Xmax : ℕ) (hX : X ≤ Xmax) :
    cutoff τ X = ∑ a ∈ Finset.range (Xmax + 1),
      newtonCoeff τ a * (X.choose a : ℤ) := by
  rw [cutoff_eq_newton_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hX))
  intro a ha hnot
  have hXa : X < a := by
    simp only [Finset.mem_range] at hnot
    omega
  simp [Nat.choose_eq_zero_of_lt hXa]

/-- Paper `lem:maskpoly`: the concrete integer polynomial value
equals the scalar mask on every certified point, including structural zeros. -/
theorem maskPoly_eq_mask (structural : Bool) (τ Xmax X : ℕ)
    (h : X ≤ Xmax ∨ structural = false) :
    maskPolyEval structural τ Xmax X = mask structural τ X := by
  cases hs : structural with
  | false => simp [maskPolyEval, mask]
  | true =>
    have hX : X ≤ Xmax := h.resolve_right (by simp [hs])
    simp only [maskPolyEval, ↓reduceIte, one_mul]
    rw [← cutoff_eq_newton_sum_of_le τ X Xmax hX]
    simp [cutoff, mask]

/-- Paper `lem:maskpoly`: explicit finite-difference coefficients;
terms with index above `τ` vanish. -/
theorem newtonCoeff_eq_sum (τ a : ℕ) :
    newtonCoeff τ a = ∑ i ∈ Finset.range (a + 1),
      (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * cutoff τ i := by
  simpa [newtonCoeff, zsmul_eq_mul] using
    (fwdDiff_iter_eq_sum_shift (1 : ℕ) (cutoff τ) a 0)

/-- Paper `lem:maskpoly`: the displayed explicit coefficient
with its exact upper index `min(a,τ)`. -/
theorem newtonCoeff_eq_sum_min (τ a : ℕ) :
    newtonCoeff τ a = ∑ i ∈ Finset.range (min a τ + 1),
      (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) := by
  rw [newtonCoeff_eq_sum]
  have hs : (∑ i ∈ Finset.range (min a τ + 1),
      (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * cutoff τ i) =
      ∑ i ∈ Finset.range (a + 1),
        (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * cutoff τ i := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left _ _)))
    intro i hi hnot
    have hiτ : τ < i := by
      simp only [Finset.mem_range] at hi hnot
      omega
    simp [cutoff, Nat.not_le.mpr hiτ]
  rw [← hs]
  apply Finset.sum_congr rfl
  intro i hi
  have hiτ : i ≤ τ := by
    simp only [Finset.mem_range] at hi
    omega
  simp [cutoff, hiτ]

/-- Paper `lem:maskpoly`: each Newton coefficient has absolute
value at most `2^a`, an explicit integer coefficient-height bound. -/
theorem newtonCoeff_abs_le (τ a : ℕ) : |newtonCoeff τ a| ≤ (2 : ℤ) ^ a := by
  rw [newtonCoeff_eq_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (a + 1),
        |(-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * cutoff τ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (a + 1), (a.choose i : ℤ) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : i ≤ τ <;> simp [cutoff, h, abs_mul, abs_pow]
    _ = (2 : ℤ) ^ a := by exact_mod_cast Nat.sum_range_choose a

/-- Paper `lem:maskpoly`: the actual integer polynomial in
the sampled residual indicator variables. -/
noncomputable def indicatorPolynomial (ι : Type*) [Fintype ι] (τ Xmax : ℕ) :
    MvPolynomial ι ℤ :=
  ∑ a ∈ Finset.range (Xmax + 1),
    MvPolynomial.C (newtonCoeff τ a) * MvPolynomial.esymm ι ℤ a

/-- Paper `lem:maskpoly`: evaluating an elementary symmetric
polynomial at the indicator of `s` gives the binomial coefficient of `s.card`. -/
theorem eval_esymm_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (a : ℕ) :
    MvPolynomial.eval (fun i => if i ∈ s then (1 : ℤ) else 0)
      (MvPolynomial.esymm ι ℤ a) = (s.card.choose a : ℤ) := by
  classical
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X,
    Finset.prod_boole]
  have hf : (Finset.univ.powersetCard a).filter (fun t : Finset ι => ∀ i ∈ t, i ∈ s) =
      s.powersetCard a := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    aesop
  have he : (∑ t ∈ Finset.univ.powersetCard a,
      if (∀ i ∈ t, i ∈ s) then (1 : ℤ) else 0) =
      ∑ _t ∈ (Finset.univ.powersetCard a).filter
        (fun t : Finset ι => ∀ i ∈ t, i ∈ s), (1 : ℤ) := by
    rw [Finset.sum_filter]
  calc
    _ = ∑ _t ∈ (Finset.univ.powersetCard a).filter
        (fun t : Finset ι => ∀ i ∈ t, i ∈ s), (1 : ℤ) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro t ht
      by_cases h : ∀ i ∈ t, i ∈ s <;> simp [h]
    _ = _ := by rw [hf]; simp [Finset.card_powersetCard]

/-- Paper `lem:maskpoly`: the actual elementary-symmetric
integer polynomial, evaluated on Boolean occurrences, equals the mask. -/
theorem indicatorPolynomial_eq_mask {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (structural : Bool) (τ Xmax : ℕ)
    (h : s.card ≤ Xmax ∨ structural = false) :
    (if structural then (1 : ℤ) else 0) *
      MvPolynomial.eval (fun i => if i ∈ s then (1 : ℤ) else 0)
        (indicatorPolynomial ι τ Xmax) = mask structural τ s.card := by
  have he : (if structural then (1 : ℤ) else 0) *
      MvPolynomial.eval (fun i => if i ∈ s then (1 : ℤ) else 0)
        (indicatorPolynomial ι τ Xmax) = maskPolyEval structural τ Xmax s.card := by
    simp only [indicatorPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
      eval_esymm_indicator, maskPolyEval]
  rw [he]
  exact maskPoly_eq_mask structural τ Xmax s.card h

end NearQuarticWires.Mask
