import Proof.Quartic.Sampler.Root
import Proof.Quartic.Cycle.TracePotential

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset Matrix
open NearCubicWires.WireExponent3_5.Shared

/-- `lem:fourier`, paper/paper.tex: the ACTUAL real matrix
dictionary, with Re/Im index independent of the lookup/parity selector index. -/
noncomputable def matrixDictionary {N G₁ G₂ : ℕ} {Z : Type}
    (R₁ R₂ : Z → Cell N → ℤ) (mask : Z → Cell N → ℝ)
    (z : Z) (t : Frequency 4 G₁ G₂ × Fin 2) (c : Cell N) : ℝ :=
  realPartMatrix t.1 (R₁ z) (R₂ z) (mask z) t.2 c

/-- `lem:fourier`, paper/paper.tex: all concrete dictionary
entries are in [-1,1], before any sampler seed is chosen. -/
theorem matrixDictionary_bounded {N G₁ G₂ : ℕ} {Z : Type}
    (R₁ R₂ : Z → Cell N → ℤ) (mask : Z → Cell N → ℝ)
    (hm : ∀ z c, |mask z c| ≤ 1) (z : Z)
    (t : Frequency 4 G₁ G₂ × Fin 2) (c : Cell N) :
    |matrixDictionary R₁ R₂ mask z t c| ≤ 1 :=
  abs_realPartMatrix_le t.1 (R₁ z) (R₂ z) (mask z) (hm z) t.2 c

/-- `lem:cycle` + `lem:root`, paper/paper.tex:
EXACT potential dock, with the same E_D, Γ and frequency dictionary on both sides.
The paper's dilation trace contributes exactly two half-traces. -/
theorem paperPotential_eq_sum_columnPotential
    {N Q G₁ G₂ : ℕ} {Z : Type} [Fintype Z]
    (R₁ R₂ : Z → Cell N → ℤ) (mask : Z → Cell N → ℝ)
    (S : Fin Q → Cell N) :
    paperPotential (matrixDictionary (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask) S =
      ∑ z : Z, NearQuarticWires.Cycle.columnPotential
        (G₁ := G₁) (G₂ := G₂) (R₁ z) (R₂ z) (mask z) S := by
  unfold paperPotential halfPotential
    NearCubicWires.WireExponent3_5.Sampler.potential
    NearQuarticWires.Cycle.columnPotential
  simp_rw [NearQuarticWires.Cycle.trace_dilation_eight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  rw [Finset.mul_sum]
  rfl

/-- `lem:fourier` + `lem:root`, paper/paper.tex:
the concrete dictionary has EXACTLY I=2|Θ| real matrices, not a duplicated
lookup/parity selector dictionary. -/
theorem matrixDictionary_card (G₁ G₂ : ℕ) :
    Fintype.card (Frequency 4 G₁ G₂ × Fin 2) =
      2 * (omega 4 G₁ * omega 4 G₂) := by
  simp [Frequency, Fintype.card_prod, ZMod.card, Nat.mul_comm]

/-- `lem:tracebound`, paper/paper.tex: the direct moment's
traceMoment is LITERALLY the trace of the concrete Cycle dilation to power eight. -/
theorem traceMoment_eq_dilation {N Q : ℕ} (D : Cell N → ℝ)
    (S : Fin Q → Cell N) :
    traceMoment D S = Matrix.trace (NearQuarticWires.Cycle.dilation
      (errorMatrix D S) ^ 8) :=
  (NearQuarticWires.Cycle.trace_dilation_eight _).symm

/-- `lem:tracebound` + `lem:cycle`, paper/paper.tex:
the concrete sum of Cycle column potentials has the signed independent-uniform
mean bound, with EXACTLY the paper's I=2|Θ| matrices and no selector duplication. -/
theorem mean_sum_columnPotential_le {N Q G₁ G₂ : ℕ} {Z : Type} [Fintype Z]
    (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (R₁ R₂ : Z → Cell N → ℤ) (mask : Z → Cell N → ℝ)
    (hm : ∀ z c, |mask z c| ≤ 1) :
    uMean (fun S : Fin Q → Cell N => ∑ z : Z,
      NearQuarticWires.Cycle.columnPotential (G₁ := G₁) (G₂ := G₂)
        (R₁ z) (R₂ z) (mask z) S) ≤
      2 * ((Fintype.card Z : ℝ) * (2 * (omega 4 G₁ * omega 4 G₂)) *
      NearCubicWires.WireExponent3_5.Sampler.C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13) := by
  simp_rw [← paperPotential_eq_sum_columnPotential]
  have h := mean_paperPotential_le hN hNQ
    (matrixDictionary (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask)
    (matrixDictionary_bounded R₁ R₂ mask hm)
  simpa only [matrixDictionary_card, Nat.cast_mul, Nat.cast_ofNat] using h

end NearQuarticWires.Sampler
