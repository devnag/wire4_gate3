import Proof.Quartic.Sampler.Basic
import Proof.Quartic.Cycle.SignProduct

set_option autoImplicit false

namespace NearQuarticWires.Cycle

open Finset

/-- Paper `lem:cycle`: alternating vertex slots of a closed walk. -/
abbrev Walk (N m : ℕ) := Fin (2 * m) → Fin N

/-- Paper `lem:cycle`: the actual row-column edge read at a walk slot. -/
def edge {N m : ℕ} (hm : 0 < m) (w : Walk N m) (l : Fin (2 * m)) :
    NearQuarticWires.Sampler.Cell N :=
  NearCubicWires.WireExponent3_5.Shared.cellOf (by omega) w l

/-- Paper `lem:cycle`: the finite enumeration of sign patterns. -/
abbrev SignPattern (m : ℕ) := Fin (2 * m) → Bool

/-- Paper `lem:cycle`: the integer sign selected by a Boolean slot. -/
def signValue (s : Bool) : ℤ := choiceSign (R := ℤ) s

/-- Paper `lem:cycle`: every enumerated integer sign has absolute value one. -/
theorem abs_signValue (s : Bool) : |signValue s| = 1 := by
  cases s <;> norm_num [signValue, choiceSign]

/-- Paper `lem:cycle`: the signed integer residual sum on the concrete walk. -/
def walkSum {N m : ℕ} (hm : 0 < m) (R : NearQuarticWires.Sampler.Cell N → ℤ)
    (σ : SignPattern m) (w : Walk N m) : ℤ :=
  ∑ l, signValue (σ l) * R (edge hm w l)

/-- Paper `lem:cycle`: its exact integer cosine/sine weight κσ. -/
def kappa (m : ℕ) (σ : SignPattern m) : ℤ :=
  1 + (-1 : ℤ) ^ m * ∏ l, signValue (σ l)

/-- Paper `lem:cycle`: the signed real product Γ_w of the actual sample-count factors. -/
def walkGamma {N Q m : ℕ} (hm : 0 < m)
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (w : Walk N m) : ℝ :=
  ∏ l, NearQuarticWires.Sampler.gamma S (edge hm w l)

/-- Paper `lem:cycle`: the mask is multiplied on every walk edge. -/
def walkMask {N m : ℕ} (hm : 0 < m)
    (mask : NearQuarticWires.Sampler.Cell N → ℝ) (w : Walk N m) : ℝ :=
  ∏ l, mask (edge hm w l)

/-- Paper `eq:ED` and `cor:conditional`:
Γ(c) as a concrete integer sum, before its real cast. -/
def gammaInt {N Q : ℕ} (S : Fin Q → NearQuarticWires.Sampler.Cell N)
    (c : NearQuarticWires.Sampler.Cell N) : ℤ :=
  ∑ j, (1 - (N : ℤ) ^ 2 * (if S j = c then 1 else 0))

/-- Paper `eq:ED`: the integer Γ agrees with the common real sampler Γ. -/
theorem gammaInt_cast {N Q : ℕ} (S : Fin Q → NearQuarticWires.Sampler.Cell N)
    (c : NearQuarticWires.Sampler.Cell N) :
    (gammaInt S c : ℝ) = NearQuarticWires.Sampler.gamma S c := by
  classical
  simp [gammaInt, NearQuarticWires.Sampler.gamma,
    NearCubicWires.WireExponent3_5.Shared.yc]

/-- Paper `cor:conditional`: the actual integer signed walk weight. -/
def walkGammaInt {N Q m : ℕ} (hm : 0 < m)
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (w : Walk N m) : ℤ :=
  ∏ l, gammaInt S (edge hm w l)

/-- Paper `cor:conditional`: no positivity is imposed on Γ_w. -/
theorem walkGammaInt_cast {N Q m : ℕ} (hm : 0 < m)
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (w : Walk N m) :
    (walkGammaInt hm S w : ℝ) = walkGamma hm S w := by
  simp [walkGammaInt, walkGamma, gammaInt_cast]

/-- Paper `lem:cycle`: the actual walk sum has no modular wrap. -/
theorem abs_walkSum_le {N m : ℕ} (hm : 0 < m)
    (R : NearQuarticWires.Sampler.Cell N → ℤ) (G : ℕ)
    (hR : ∀ c, |R c| ≤ G) (σ : SignPattern m) (w : Walk N m) :
    |walkSum hm R σ w| ≤ (2 * m : ℕ) * (G : ℤ) := by
  classical
  calc
    |walkSum hm R σ w| ≤ ∑ l, |signValue (σ l) * R (edge hm w l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin (2 * m), (G : ℤ) := by
      apply Finset.sum_le_sum
      intro l _
      simpa only [abs_mul, abs_signValue, one_mul] using hR (edge hm w l)
    _ = _ := by simp

end NearQuarticWires.Cycle
