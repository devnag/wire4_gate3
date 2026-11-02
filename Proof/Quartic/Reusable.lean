import Batteries.Tactic.Alias
import Proof.Quartic.Tomography
import Proof.Gates.ScalarReconstruction
import Proof.Quartic.Mask.Polynomial
import Proof.Quartic.Cycle.Identity
import Proof.Quartic.Cells.MeanPopulation
import Proof.Quartic.Transfer.Reconcile4

/-!
# Results of independent interest

Each declaration here is a name for a theorem proved elsewhere in this repository, with a plain statement, so that
other work can cite it with `import Proof.Quartic.Reusable`. The two-dimensional modular tomography theorems are in
`Proof/Quartic/Tomography.lean` (namespace `NearQuarticWires.Tomography`), which this module imports.

* One-dimensional modular tomography: `scalarCounts_determine`, `scalar_reconstruct`.
* Threshold masks as integer polynomials in the population: `threshold_eq_newton_sum`.
* The cycle-sum identity: `cycle_sum_identity`.
* Product-star cells, mean population: `mean_population`.
* The black-box transfer from a certified counter to the wire lower bound: `wireTransfer`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reusable

open NearCubicGates NearCubicGates.Reconstruction NearCubicGates.ScalarWindow
open scoped BigOperators Matrix

/-- **One-dimensional modular tomography: residue counts determine the function.** For a nonempty finite set `P` of
primes with window `W = 1 + Σ_{p ∈ P} (p − 1)` and `L ≤ W`, a rational function `f` on `{lo, …, lo + L − 1}` is
determined by its residue counts `Σ { f(x) : x ≡ a (mod p) }` (`p ∈ P`, `a ∈ ℤ/p`), the entries of
`scalarMatrix P lo L *ᵥ f`. -/
theorem scalarCounts_determine (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo : ℤ) (L : ℕ) (hL : L ≤ window primes) :
    Function.Injective (fun f : Fin L → ℚ => scalarMatrix primes lo L *ᵥ f) :=
  scalarMatrix_injective primes hne hprime lo L hL

/-- **One-dimensional modular tomography: reconstruction.** Under the hypotheses of `scalarCounts_determine`, a
rational left inverse `R` of the count matrix exists, is accepted by the exact check `leftInverseCheck`, and recovers
every function from its residue counts. -/
theorem scalar_reconstruct (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo : ℤ) (L : ℕ) (hL : L ≤ window primes) :
    ∃ R : Matrix (Fin L) (ResidueRow (fun p : primes => p.val)) ℚ,
      leftInverseCheck (scalarMatrix primes lo L) R = true ∧
      ∀ f : Fin L → ℚ, R *ᵥ (scalarMatrix primes lo L *ᵥ f) = f :=
  scalar_reconstruction_complete primes hne hprime lo L hL

/-- **Threshold masks are integer polynomials in the population.** For natural numbers `X ≤ X_max` and a threshold
`τ`, `[X ≤ τ] = Σ_{a=0}^{X_max} c_a(τ) · C(X, a)` with the integer coefficients
`c_a(τ) = Σ_{i=0}^{a} (−1)^{a−i} C(a, i) [i ≤ τ]`, which do not depend on `X` (`lem:maskpoly`). -/
theorem threshold_eq_newton_sum (τ X Xmax : ℕ) (hX : X ≤ Xmax) :
    (if X ≤ τ then (1 : ℤ) else 0) = ∑ a ∈ Finset.range (Xmax + 1),
      (∑ i ∈ Finset.range (a + 1), (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ) * (if i ≤ τ then 1 else 0)) *
        (X.choose a : ℤ) := by
  have h := Mask.cutoff_eq_newton_sum_of_le τ X Xmax hX
  simp only [Mask.newtonCoeff_eq_sum] at h
  simpa only [Mask.cutoff] using h

/-- **The cycle-sum identity** (`lem:cycle`, at `m = 4`). Let `R₁, R₂ : Cell N → ℤ` be scores with `|R₁| ≤ G₁` and
`|R₂| ≤ G₂`, `mask : Cell N → ℝ` a weight and `S` a list of `Q` sample cells. The column potential
`Σ_θ Σ_ν tr(D(E_{θ,ν})^8)` (`θ` over the `(16G₁+1)(16G₂+1)` frequencies of `ZMod (16G₁+1) × ZMod (16G₂+1)`, `ν` over
the real and imaginary parts of the masked phases, `E_{θ,ν}` the sampled error matrix and `D(E)` its dilation
`[[0, E], [Eᵀ, 0]]`) equals
`(2·(16G₁+1)(16G₂+1)/4^4) · Σ_w Γ_w · mask_w · Σ_σ κ_σ [Σ_l σ_l R₁(c_l(w)) = 0] [Σ_l σ_l R₂(c_l(w)) = 0]`.
Here `w` ranges over the closed walks `w : Fin 8 → Fin N` of eight steps; step `l` reads the cell
`c_l(w) = (w_l, w_{l+1})` for even `l` and `(w_{l+1}, w_l)` for odd `l` (indices mod 8, so rows and columns
alternate). `Γ_w = ∏_l Γ(c_l(w))` and `mask_w = ∏_l mask(c_l(w))` are products over the eight steps, `Γ(c)` being
the sample-count factor of `S`; `σ` ranges over the sign patterns `{±1}^8`, and `κ_σ = 1 + ∏_l σ_l`. Only walks
whose two signed score sums vanish exactly contribute. -/
alias cycle_sum_identity := NearQuarticWires.Cycle.cycle_sum_identity

/-- **Product-star cells: mean population** (`lem:meanpop`). For star parameters `P` and normalized threshold gates
whose supports have total size at most `W`, some translation `σ` has mean cell population at most
`6 · r^{3/2} · W / n^{3/2}`. -/
alias mean_population := NearQuarticWires.Cells.mean_population

/-- **The transfer from the counter to the wire bound** (`thm:counter` to `thm:main`). From the eight intermediate
inputs (`NineInputs`) and a counter satisfying the contract `Transfer.CounterExists4`, the near-quartic wire lower
bound `FinalStatement4` follows. The contract asks, for every pair of positive exponents `B₁, B₂`, for one
program with the properties (i)–(iii) of `thm:counter` at the cap `W ≤ a·β·𝒜₄(n)`,
`𝒜₄(n) = n^4/(λ_n^{17/4} μ_n^{15/2})` (`Transfer.Counter4`). The transfer is proved for this cap only. -/
alias wireTransfer := NearQuarticWires.Transfer.transfer4_official

end NearQuarticWires.Reusable
