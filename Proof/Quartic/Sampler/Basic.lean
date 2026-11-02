import Proof.Wire_3_5.RowsFourier
import Proof.Wire_3_5.SamplerPotential

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset Matrix

abbrev Cell (N : ℕ) := NearCubicWires.WireExponent3_5.Shared.Cell N

/-- `lem:fourier`, paper/paper.tex: the actual Fourier modulus. -/
def omega (m G : ℕ) : ℕ := 4 * m * G + 1

instance omega_neZero (m G : ℕ) : NeZero (omega m G) := ⟨by unfold omega; omega⟩

/-- `lem:fourier`, paper/paper.tex: the two-score character group. -/
abbrev Frequency (m G₁ G₂ : ℕ) := ZMod (omega m G₁) × ZMod (omega m G₂)

/-- `eq:ED`, paper/paper.tex: the common sample-count factor Γ. -/
def gamma {N Q : ℕ} (S : Fin Q → Cell N) (c : Cell N) : ℝ :=
  ∑ j, NearCubicWires.WireExponent3_5.Shared.yc N (S j) c

/-- `eq:ED`, paper/paper.tex: the concrete real error matrix E_D. -/
abbrev errorMatrix {N Q : ℕ} (D : Cell N → ℝ) (S : Fin Q → Cell N) :=
  NearCubicWires.WireExponent3_5.Sampler.errMatrix D S

/-- `eq:ED`, paper/paper.tex: E_D(c)=D(c)Γ(c), for signed D. -/
theorem errorMatrix_apply {N Q : ℕ} (D : Cell N → ℝ) (S : Fin Q → Cell N)
    (u v : Fin N) : errorMatrix D S u v = D (u, v) * gamma S (u, v) := rfl

/-- `eq:ED`, paper/paper.tex: the sample-count expression for E_D. -/
theorem errorMatrix_explicit {N Q : ℕ} (D : Cell N → ℝ)
    (S : Fin Q → Cell N) (u v : Fin N) :
    errorMatrix D S u v = (Q : ℝ) * D (u, v) - (N : ℝ) ^ 2 *
      ∑ j, (if S j = (u, v) then 1 else 0) * D (u, v) :=
  NearCubicWires.WireExponent3_5.Sampler.ecell_eq D S (u, v)

/-- `lem:fourier`, paper/paper.tex: the residual character. -/
noncomputable def phase {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂)
    (R₁ R₂ : ℤ) : ℂ :=
  NearCubicWires.WireExponent3_5.Rows.chi (θ.1 * (R₁ : ZMod (omega m G₁))) *
    NearCubicWires.WireExponent3_5.Rows.chi (θ.2 * (R₂ : ZMod (omega m G₂)))

/-- `lem:fourier`, paper/paper.tex: every residual phase is unimodular. -/
theorem norm_phase {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂) (R₁ R₂ : ℤ) :
    ‖phase θ R₁ R₂‖ = 1 := by
  simp [phase, NearCubicWires.WireExponent3_5.Rows.norm_chi]

/-- `lem:fourier`, paper/paper.tex: integer residual phases add. -/
theorem phase_add {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂)
    (R₁ R₂ S₁ S₂ : ℤ) :
    phase θ (R₁ + S₁) (R₂ + S₂) = phase θ R₁ R₂ * phase θ S₁ S₂ := by
  simp only [phase, Int.cast_add, mul_add,
    NearCubicWires.WireExponent3_5.Rows.chi_add]
  ring

/-- `lem:fourier`, paper/paper.tex: zero residual has phase one. -/
@[simp] theorem phase_zero {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂) :
    phase θ 0 0 = 1 := by
  simp [phase, NearCubicWires.WireExponent3_5.Rows.chi_zero]

/-- `lem:fourier`, paper/paper.tex: frequency zero detects the mask. -/
@[simp] theorem phase_zero_frequency {m G₁ G₂ : ℕ} (R₁ R₂ : ℤ) :
    phase (0 : Frequency m G₁ G₂) R₁ R₂ = 1 := by
  simp [phase, NearCubicWires.WireExponent3_5.Rows.chi_zero]

/-- `lem:fourier`, paper/paper.tex: negation inverts the phase. -/
theorem phase_neg {m G₁ G₂ : ℕ} (θ : Frequency m G₁ G₂) (R₁ R₂ : ℤ) :
    phase θ (-R₁) (-R₂) = (phase θ R₁ R₂)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← phase_add]
  simp

/-- `lem:fourier`, paper/paper.tex: the mask is INSIDE M_θ. -/
noncomputable def maskedPhase {m G₁ G₂ N : ℕ} (θ : Frequency m G₁ G₂)
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (c : Cell N) : ℂ :=
  phase θ (R₁ c) (R₂ c) * (mask c : ℂ)

/-- `lem:fourier`, paper/paper.tex: ν independently selects Re/Im. -/
noncomputable def realPartMatrix {m G₁ G₂ N : ℕ} (θ : Frequency m G₁ G₂)
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (ν : Fin 2) (c : Cell N) : ℝ :=
  if ν = 0 then (maskedPhase θ R₁ R₂ mask c).re
  else (maskedPhase θ R₁ R₂ mask c).im

/-- `lem:fourier`, paper/paper.tex: the real component API. -/
@[simp] theorem realPartMatrix_zero {m G₁ G₂ N : ℕ} (θ : Frequency m G₁ G₂)
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (c : Cell N) :
    realPartMatrix θ R₁ R₂ mask 0 c = (maskedPhase θ R₁ R₂ mask c).re := by
  simp [realPartMatrix]

/-- `lem:fourier`, paper/paper.tex: the imaginary component API. -/
@[simp] theorem realPartMatrix_one {m G₁ G₂ N : ℕ} (θ : Frequency m G₁ G₂)
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (c : Cell N) :
    realPartMatrix θ R₁ R₂ mask 1 c = (maskedPhase θ R₁ R₂ mask c).im := by
  simp [realPartMatrix]

/-- `lem:fourier`, paper/paper.tex: D_{θ,ν} has entries in [-1,1]. -/
theorem abs_realPartMatrix_le {m G₁ G₂ N : ℕ} (θ : Frequency m G₁ G₂)
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ)
    (hmask : ∀ c, |mask c| ≤ 1) (ν : Fin 2) (c : Cell N) :
    |realPartMatrix θ R₁ R₂ mask ν c| ≤ 1 := by
  have hnorm : ‖maskedPhase θ R₁ R₂ mask c‖ ≤ 1 := by
    simpa [maskedPhase, norm_mul, norm_phase] using hmask c
  unfold realPartMatrix
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans hnorm
  · exact (Complex.abs_im_le_norm _).trans hnorm

end NearQuarticWires.Sampler
