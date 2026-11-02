import Proof.Quartic.Statement.Final

/-!
# The joint statement: `thm:main` (wires) and `thm:gates` (charged top weight)

The joint paper states two results for the same constants:

* `thm:main` (Theorem 1.1): every `SYM∘THR` circuit `C` on `n ≥ n₀` inputs with
  `W(C) ≤ ⌊n^4/(K_d λ_n^{17/4} μ_n^{15/2})⌋` has `agr(C, F_d) < 1 − d`;
* `thm:gates` (Corollary 1.2): with `γ`, `d`, `K_d`, `F_d` and `n_0` as in `thm:main`, for every `n ≥ n_0`, every
  `SYM∘THR` circuit `C` on `n` inputs with at most `⌊n^3/(2K_d λ_n^{17/4} μ_n^{15/2})⌋` gates has
  `agr(C, F_d) < 1 − d`; more generally, so does every circuit `C(x) = g(Σ_i c_i T_i(x))` with integer `c_i ≠ 0` and
  charged top weight `Σ_i |c_i|` at most that cap.

The class `𝒲` (Definition 1.1) consists of circuits `C(x) = g(Σ_i c_i T_i(x))` with `c_i ∈ ℤ ∖ {0}` and
`g : ℤ → {0,1}`, and its charged top weight is `wt(C) = Σ_i |c_i|`. This is `NearCubicGates.Target.WeightedSymmetricCircuit`
with `topWeight` and `agreement`, the class of the near-cubic gate theorem `NearCubicGates.Target.MainStatement`.

`JointStatement4` keeps the paper's sharing: one `γ`, and for each `d` one `K_d`, one `F_d` and one `n₀` serve every
conclusion. `FinalStatement4` and `GateStatement4` are its two halves, each with its own constants.

The release statement (`Release.lean`) adds the published results as hypotheses. No proof is in this file.
-/

set_option autoImplicit false

namespace NearQuarticWires.Statement

open NearCubicWires NearCubicGates.Target

/-- The boxed cap of `thm:gates`, literally: `⌊n^3 / (2 K λ_n^{17/4} μ_n^{15/2})⌋`, with the same `λ_n`, `μ_n` and
real powers as `wireCap`, and the floor taken in `ℕ`. -/
noncomputable def gateCap (K n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ 3 /
      (2 * (K : ℝ) * (lambda n : ℝ) ^ ((17 : ℝ) / 4) * (mu n : ℝ) ^ ((15 : ℝ) / 2))⌋₊

/-- The gate count conclusion of `thm:gates` for constants `K`, `F`, `d` at length `n`: every `SYM∘THR` circuit on
`n` inputs with at most `gateCap K n` gates (occurrences, `G = C.bottomCount`) agrees with `F` on less than a `1 − d`
fraction of inputs. -/
def SymGatesAt (K : ℕ) (F : Language) (d : ℝ) (n : ℕ) : Prop :=
  ∀ C : SymmetricThresholdCircuit n, C.bottomCount ≤ gateCap K n → agr C F < 1 - d

/-- The general form of `thm:gates` for constants `K`, `F`, `d` at length `n`: every circuit `g(Σ_i c_i T_i)` with
integer top weights (the class `𝒲` of the near-cubic gate theorem) on `n` inputs with charged top weight
`Σ_i |c_i|` at most `gateCap K n` agrees with `F` on less than a `1 − d` fraction of inputs. -/
def GatesAt (K : ℕ) (F : Language) (d : ℝ) (n : ℕ) : Prop :=
  ∀ C : WeightedSymmetricCircuit n, C.topWeight ≤ gateCap K n → agreement C F < 1 - d

/-- The conclusion of `thm:main` for constants `K`, `F`, `d` at length `n`. -/
def WiresAt (K : ℕ) (F : Language) (d : ℝ) (n : ℕ) : Prop :=
  ∀ C : SymmetricThresholdCircuit n, wires C ≤ wireCap K n → agr C F < 1 - d

/-- `thm:main` and `thm:gates` together for a fixed rational `γ`: for every fixed `0 < d < γ/5` there are a
positive integer `K_d`, a language `F_d ∈ E^NP` and `n₀ ≥ 4` such that all three conclusions (wires, gates, weighted
gates) hold at every `n ≥ n₀`. -/
def JointAt4 (gamma : ℚ) : Prop :=
  ∀ d : ℝ, 0 < d → d < (gamma : ℝ) / 5 →
    ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
      ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → WiresAt K F d n ∧ SymGatesAt K F d n ∧ GatesAt K F d n

/-- **The joint theorem** (`thm:main` and `thm:gates`), with `γ` quantified as in `FinalStatement4`. -/
def JointStatement4 : Prop :=
  ∃ gamma : ℚ, 0 < gamma ∧ gamma < 1 ∧ JointAt4 gamma

/-- `thm:gates` alone: the near-cubic gate lower bound with the cap `⌊n^3/(2K λ_n^{17/4} μ_n^{15/2})⌋`, for `SYM∘THR`
gate count and for charged top weight. -/
def GateStatement4 : Prop :=
  ∃ gamma : ℚ, 0 < gamma ∧ gamma < 1 ∧
    ∀ d : ℝ, 0 < d → d < (gamma : ℝ) / 5 →
      ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
        ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → SymGatesAt K F d n ∧ GatesAt K F d n

end NearQuarticWires.Statement
