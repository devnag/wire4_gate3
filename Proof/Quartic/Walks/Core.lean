import Proof.Gates.SampledChainMoments
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Integer occurrence contributions to the paper's signed walk sums.
The index type counts occurrences, so duplicate bottom gates remain distinct.
-/

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators

variable {Occ : Type*} [Fintype Occ]

/-- Paper `sec:walks`, paper/paper.tex: the contribution `c_{j,t}` of one
occurrence along the `2m` edge slots of a concrete closed walk. -/
def contribution {m : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ) (t : Occ) : ℤ :=
  ∑ l, sigma l * delta t l

/-- Paper `sec:walks`, paper/paper.tex: the signed walk sum `Y_{j,sigma}`. -/
def walkSum {m : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ) : ℤ :=
  ∑ t, contribution sigma delta t

/-- Paper `sec:walks`, paper/paper.tex: the proposed sampled walk sum `K_r`;
the witness coefficients are integers, so this definition also covers dishonest
proposals without making a sampling assumption. -/
def sampledSum {m : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ) (xi : ℕ → Occ → ℤ) (r : ℕ) : ℤ :=
  ∑ t, xi r t * contribution sigma delta t

/-- Paper `lem:cycle`/`sec:walks`, paper/paper.tex: summing occurrence
contributions is exactly the edgewise signed residual sum. -/
theorem walkSum_eq_edge_sum {m : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ) :
    walkSum sigma delta = ∑ l, sigma l * ∑ t, delta t l := by
  classical
  simp only [walkSum, contribution, Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype Occ] in
/-- Paper `lem:localize`, paper/paper.tex: every occurrence summand `c_t`
has absolute value at most `2m`, including repeated walk edges. -/
theorem contribution_abs_le {m : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ)
    (hsigma : ∀ l, |sigma l| ≤ 1) (hdelta : ∀ t l, |delta t l| ≤ 1) (t : Occ) :
    |contribution sigma delta t| ≤ (2 * m : ℕ) := by
  classical
  calc
    _ ≤ ∑ l : Fin (2 * m), |sigma l * delta t l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin (2 * m), (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hsigma l)).trans (hdelta t l)
    _ = _ := by simp

/-- Paper `lem:localize`, paper/paper.tex: the absolute occurrence mass is
bounded by the sum of the actual mixed populations along all walk edges. -/
theorem contribution_mass_le {m : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ) (hsigma : ∀ l, |sigma l| ≤ 1) :
    (∑ t, |contribution sigma delta t|) ≤ ∑ l, ∑ t, |delta t l| := by
  classical
  calc
    _ ≤ ∑ t, ∑ l : Fin (2 * m), |delta t l| := by
      apply Finset.sum_le_sum
      intro t _
      calc
        _ ≤ ∑ l : Fin (2 * m), |sigma l * delta t l| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro l _
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hsigma l)
    _ = _ := Finset.sum_comm

/-- Paper `lem:localize`, paper/paper.tex: under the actual per-edge
population cap `16U`, the walk has absolute mass at most `ell0=32mU`. -/
theorem contribution_mass_le_ell0 {m U : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ) (hsigma : ∀ l, |sigma l| ≤ 1)
    (hpop : ∀ l, (∑ t, |delta t l|) ≤ (16 * U : ℕ)) :
    (∑ t, |contribution sigma delta t|) ≤ (32 * m * U : ℕ) := by
  classical
  calc
    _ ≤ ∑ l : Fin (2 * m), ∑ t, |delta t l| := contribution_mass_le sigma delta hsigma
    _ ≤ ∑ _l : Fin (2 * m), ((16 * U : ℕ) : ℤ) :=
      Finset.sum_le_sum (fun l _ => hpop l)
    _ = _ := by simp; ring

/-- Paper `lem:localize`, paper/paper.tex: the concrete walk sum is bounded
by its occurrence mass, the hypothesis used by the initial nested-rate digit. -/
theorem walkSum_abs_le_mass {m : ℕ} (sigma : Fin (2 * m) → ℤ)
    (delta : Occ → Fin (2 * m) → ℤ) :
    |walkSum sigma delta| ≤ ∑ t, |contribution sigma delta t| :=
  Finset.abs_sum_le_sum_abs _ _

end NearQuarticWires.Walks
