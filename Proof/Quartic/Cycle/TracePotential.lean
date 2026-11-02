import Proof.Quartic.Cycle.Basic
import Proof.Wire_3_5.SamplerTrace

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset Matrix
open NearQuarticWires.Sampler

/-- Paper `eq:ED` and `lem:cycle`: the actual real dilation. -/
def dilation {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks 0 E E.transpose 0

/-- Paper `lem:cycle`: the dilation's eighth trace is twice the half-trace. -/
theorem trace_dilation_eight {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace (dilation E ^ 8) = 2 * Matrix.trace ((E * E.transpose) ^ 4) := by
  have hsquare : dilation E ^ 2 =
      Matrix.fromBlocks (E * E.transpose) 0 0 (E.transpose * E) := by
    simp [dilation, pow_two, Matrix.fromBlocks_multiply]
  have hpow : dilation E ^ 8 =
      Matrix.fromBlocks ((E * E.transpose) ^ 4) 0 0 ((E.transpose * E) ^ 4) := by
    calc
      _ = (dilation E ^ 2) ^ 4 := by rw [← pow_mul]
      _ = _ := by rw [hsquare, Matrix.fromBlocks_diagonal_pow]
  rw [hpow]
  have htrace (A B : Matrix (Fin N) (Fin N) ℝ) :
      Matrix.trace (Matrix.fromBlocks A 0 0 B) = Matrix.trace A + Matrix.trace B := by
    simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  rw [htrace, NearCubicWires.WireExponent3_5.Sampler.trace_transpose_mul_pow]
  ring

/-- Paper `lem:cycle`: the concrete m=4 column potential Φ_z. -/
noncomputable def columnPotential {N Q G₁ G₂ : ℕ}
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (S : Fin Q → Cell N) : ℝ :=
  ∑ θ : Frequency 4 G₁ G₂, ∑ ν : Fin 2,
    Matrix.trace (dilation (errorMatrix (realPartMatrix θ R₁ R₂ mask ν) S) ^ 8)

/-- Paper `lem:cycle`: Φ_z expands over the concrete alternating eight-edge walks. -/
theorem columnPotential_walks {N Q G₁ G₂ : ℕ}
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (S : Fin Q → Cell N) :
    columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S =
      2 * ∑ θ : Frequency 4 G₁ G₂, ∑ ν : Fin 2, ∑ w : Walk N 4,
        ∏ l, (realPartMatrix θ R₁ R₂ mask ν (edge (by norm_num) w l) *
          gamma S (edge (by norm_num) w l)) := by
  unfold columnPotential
  simp_rw [trace_dilation_eight,
    ← NearCubicWires.WireExponent3_5.Sampler.walkMoment_eq_trace]
  simp only [← Finset.mul_sum]
  rfl

end NearQuarticWires.Cycle
