import Proof.Gates.PairReconstruction
import Proof.Gates.QuantitativePairWindow

/-!
# Modular discrete tomography

A rational function on an integer square is determined by its counts modulo a set of primes, once the square is
small enough for the primes. This module restates the result, proved in the near-cubic gate companion's
`Proof/Gates/PairReconstruction.lean`, under names meant for citation:

* `residueCounts P lo₁ lo₂ L f`: for a finite set `P` of primes, the box
  `B = {lo₁, …, lo₁ + L − 1} × {lo₂, …, lo₂ + L − 1}` (indexed by `Fin L × Fin L`) and `f : B → ℚ`, the value at
  `⟨p, (a, b)⟩` (`p ∈ P`, `a, b ∈ ℤ/p`) is `Σ { f(x, y) : (x, y) ∈ B, x ≡ a, y ≡ b (mod p) }`
  (`residueCounts_apply`).
* `residueCounts_determine`: if `P` is nonempty, `L ≥ 2` and `L ≤ S(⌊(W − 1)/(L − 1)⌋)`, where
  `W = 1 + Σ_{p ∈ P} (p − 1)` (`NearCubicGates.ScalarWindow.window`) and `S(q) = Σ_{m=1}^{q} m·φ(m)`
  (`NearCubicGates.TomographyDirections.degreeSum`), then `f ↦ residueCounts P lo₁ lo₂ L f` is injective.
* `reconstruct`: under the same hypotheses there is a rational matrix `R`, accepted by the exact rational check
  `leftInverseCheck` (`R · A = 1` for the count matrix `A`), with `R · residueCounts P lo₁ lo₂ L f = f` for every `f`.
* `reconstruct_at_side`: the side `side W = ⌊⌊√⌊√W⌋⌋³/24⌋` meets the hypothesis once `W` is large, and
  `side W ^ 4 ≤ W ^ 3 ≤ 16³·48⁴·side W ^ 4` (`side_bounds`), so boxes of side of order `W^{3/4}` are reconstructible.

Running time: `R` is found by exact Gaussian elimination over `ℚ` on the `(Σ_{p ∈ P} p²) × L²` zero-one count matrix,
polynomial in `L`, `Σ_{p ∈ P} p²` and the bit length of the data. This running time is not formalized here.

Usage: `import Proof.Quartic.Tomography`, then
`NearQuarticWires.Tomography.residueCounts_determine P hne hprime lo₁ lo₂ L hL hsize h : f = g`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Tomography

open NearCubicGates NearCubicGates.Reconstruction NearCubicGates.ScalarWindow NearCubicGates.TomographyDirections
open scoped BigOperators Matrix

/-- The residue counts of `f` on the box with corner `(lo₁, lo₂)` and side `L`, for the primes of `primes`: at the
row `⟨p, (a, b)⟩` the sum of `f` over the points `(lo₁ + x, lo₂ + y)` of the box with `lo₁ + x ≡ a` and
`lo₂ + y ≡ b (mod p)` (`residueCounts_apply`). -/
def residueCounts (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (L : ℕ) (f : Fin L × Fin L → ℚ) :
    PairResidueRow (fun p : primes => p.val) → ℚ :=
  pairMatrix primes lo₁ lo₂ L *ᵥ f

/-- The residue counts, pointwise. -/
theorem residueCounts_apply (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (L : ℕ) (f : Fin L × Fin L → ℚ)
    (p : primes) (a b : Fin p.val) :
    residueCounts primes lo₁ lo₂ L f ⟨p, (a, b)⟩ =
      ∑ i : Fin L × Fin L,
        if (lo₁ + (i.1.val : ℤ)) % (p.val : ℤ) = (a.val : ℤ) ∧
            (lo₂ + (i.2.val : ℤ)) % (p.val : ℤ) = (b.val : ℤ) then f i else 0 := by
  simp only [residueCounts, pairMatrix, pairResidueMatrix, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul]

/-- **Residue counts determine the function.** For a nonempty finite set of primes with window
`W = 1 + Σ_p (p − 1)` and a side `2 ≤ L ≤ S(⌊(W − 1)/(L − 1)⌋)`, two rational functions on an `L × L` integer box
with the same residue counts are equal. -/
theorem residueCounts_determine (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (L : ℕ) (hL : 2 ≤ L) (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1)))
    {f g : Fin L × Fin L → ℚ} (h : residueCounts primes lo₁ lo₂ L f = residueCounts primes lo₁ lo₂ L g) :
    f = g :=
  pairMatrix_injective primes hne hprime lo₁ lo₂ L hL hsize h

/-- **Reconstruction.** Under the hypotheses of `residueCounts_determine`, a rational left inverse `R` of the count
matrix exists, is accepted by the exact check `leftInverseCheck`, and recovers every function from its residue
counts. -/
theorem reconstruct (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (L : ℕ) (hL : 2 ≤ L) (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1))) :
    ∃ R : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes => p.val)) ℚ,
      leftInverseCheck (pairMatrix primes lo₁ lo₂ L) R = true ∧
      ∀ f : Fin L × Fin L → ℚ, R *ᵥ residueCounts primes lo₁ lo₂ L f = f :=
  pair_reconstruction_complete primes hne hprime lo₁ lo₂ L hL hsize

/-- The computable side `side W = ⌊⌊√⌊√W⌋⌋³/24⌋` is of order `W^{3/4}`. -/
theorem side_bounds (W : ℕ) (hW : 4 ^ 4 ≤ W) :
    QuantitativePairWindow.side W ^ 4 ≤ W ^ 3 ∧ W ^ 3 ≤ (16 ^ 3 * 48 ^ 4) * QuantitativePairWindow.side W ^ 4 :=
  QuantitativePairWindow.side_three_quarters W hW

/-- **Reconstruction at side of order `W^{3/4}`.** For every nonempty finite set of primes whose window `W` is large
enough, every rational function on a box of side `side W` is recovered from its residue counts by a checked rational
left inverse. -/
theorem reconstruct_at_side :
    ∃ onset : ℕ, ∀ (primes : Finset ℕ), primes.Nonempty → (∀ p ∈ primes, Nat.Prime p) →
      onset ^ 4 ≤ window primes → ∀ lo₁ lo₂ : ℤ,
      ∃ R : Matrix (Fin (QuantitativePairWindow.side (window primes)) × Fin (QuantitativePairWindow.side (window primes)))
          (PairResidueRow (fun p : primes => p.val)) ℚ,
        leftInverseCheck (pairMatrix primes lo₁ lo₂ (QuantitativePairWindow.side (window primes))) R = true ∧
        ∀ f, R *ᵥ residueCounts primes lo₁ lo₂ (QuantitativePairWindow.side (window primes)) f = f := by
  obtain ⟨onset, _, h⟩ := QuantitativePairWindow.side_is_admissible
  refine ⟨onset, fun primes hne hprime hW lo₁ lo₂ => ?_⟩
  obtain ⟨hL, hsize⟩ := h (window primes) hW
  exact reconstruct primes hne hprime lo₁ lo₂ _ hL hsize

end NearQuarticWires.Tomography
