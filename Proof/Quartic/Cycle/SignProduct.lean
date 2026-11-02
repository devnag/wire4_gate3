import Mathlib

set_option autoImplicit false

namespace NearQuarticWires.Cycle

open Finset

/-- Paper `lem:cycle`: expand the exponential choices in the cosine product. -/
theorem prod_add_eq_sum_bool {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (a b : ι → R) :
    (∏ i, (a i + b i)) =
      ∑ σ : ι → Bool, ∏ i, if σ i then a i else b i := by
  classical
  simpa using
    (Fintype.prod_sum (fun i (s : Bool) => if s then a i else b i))

/-- Paper `lem:cycle`: the sign of the chosen sine exponential. -/
def choiceSign {R : Type*} [Ring R] (s : Bool) : R := if s then 1 else -1

/-- Paper `lem:cycle`: signed exponential-product expansion. -/
theorem prod_sub_eq_sum_bool {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (a b : ι → R) :
    (∏ i, (a i - b i)) =
      ∑ σ : ι → Bool, (∏ i, choiceSign (R := R) (σ i)) *
        ∏ i, if σ i then a i else b i := by
  classical
  rw [show (∏ i, (a i - b i)) = ∏ i, (a i + (-b i)) by
    congr 1; funext i; ring]
  rw [prod_add_eq_sum_bool]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp [choiceSign]

/-- Paper `lem:cycle`: algebraic core of the cosine-plus-sine coefficient.
Specializing the number of slots to 2m gives kappa = 1 + (-1)^m product signs. -/
theorem cycle_sign_product {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (a b : ι → R) (m : ℕ) :
    (∏ i, (a i + b i)) + (-1 : R)^m * (∏ i, (a i - b i)) =
      ∑ σ : ι → Bool,
        (1 + (-1 : R)^m * ∏ i, choiceSign (R := R) (σ i)) *
          ∏ i, if σ i then a i else b i := by
  classical
  rw [prod_add_eq_sum_bool, prod_sub_eq_sum_bool, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  ring

#print axioms cycle_sign_product

end NearQuarticWires.Cycle
