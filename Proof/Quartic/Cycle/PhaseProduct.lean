import Proof.Quartic.Cycle.Basic
import Proof.Quartic.Cycle.CharacterSum

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler

/-- Paper `lem:cycle`: negating a residual conjugates its actual Fourier phase. -/
theorem phase_neg_star {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂) (a b : ℤ) :
    phase θ (-a) (-b) = star (phase θ a b) := by
  rw [phase_neg]
  exact Complex.inv_eq_conj (norm_phase θ a b)

/-- Paper `lem:cycle`: the finite phase product adds both integer residuals. -/
theorem phase_finset_sum {ι : Type*} [DecidableEq ι]
    {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂)
    (a b : ι → ℤ) (s : Finset ι) :
    phase θ (∑ i ∈ s, a i) (∑ i ∈ s, b i) = ∏ i ∈ s, phase θ (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, phase_add, ih]

/-- Paper `lem:cycle`: each exponential choice is exactly a signed residual phase. -/
theorem phase_choice {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂)
    (a b : ℤ) (s : Bool) :
    (if s then phase θ a b else star (phase θ a b)) =
      phase θ (signValue s * a) (signValue s * b) := by
  cases s <;> simp [signValue, choiceSign, phase_neg_star]

/-- Paper `lem:cycle`: the actual sign-pattern product on all walk edges. -/
theorem walk_phase_product {N m G₁ G₂ : ℕ} (hm : 0 < m)
    (θ : Frequency m G₁ G₂) (R₁ R₂ : Cell N → ℤ)
    (σ : SignPattern m) (w : Walk N m) :
    (∏ l, if σ l then phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l))
      else star (phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l)))) =
      phase θ (walkSum hm R₁ σ w) (walkSum hm R₂ σ w) := by
  simp_rw [phase_choice]
  exact (phase_finset_sum θ _ _ Finset.univ).symm

/-- Paper `lem:cycle`: exact frequency orthogonality for the two residual walk sums. -/
theorem sum_phase {m G₁ G₂ : ℕ} (a b : ℤ) :
    (∑ θ : Frequency m G₁ G₂, phase θ a b) =
      ((omega m G₁ : ℕ) : ℂ) * (omega m G₂ : ℂ) *
        (if (a : ZMod (omega m G₁)) = 0 then 1 else 0) *
        (if (b : ZMod (omega m G₂)) = 0 then 1 else 0) := by
  classical
  simpa only [Frequency, Fintype.sum_prod_type, phase,
    NearCubicWires.WireExponent3_5.Rows.chi] using
      two_score_character_sum (a : ZMod (omega m G₁)) (b : ZMod (omega m G₂))

end NearQuarticWires.Cycle
