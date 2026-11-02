import Proof.Quartic.Transfer.Counter4
import Proof.Gates.Main.Statement

/-!
# The working form of the wire-4 main theorem: `FinalStatement4'`

Paper: `thm:main` (Theorem 1.2, `paper/paper.tex`) with `def:class`. For every fixed
`0 < d < γ/5` there are `K_d > 0` and `F_d ∈ E^NP` such that, for all large `n`, every `SYM∘THR` circuit `C` on `n`
inputs with `W(C) ≤ ⌊n⁴ / (K_d λ_n^{17/4} μ_n^{15/2})⌋` has `agr(C, F_d) < 1 − d`. `γ` is the rational gap of the
three-query PCPP input, quantified as in the base's `MainStatement`.

Vocabulary: `SymmetricThresholdCircuit` and its `wireCount = Σ_i (|support T_i| + 1) = G + Σ_i f_i` (shared
`NearCubicWires` library, `Proof/Foundations/Semantics.lean`); `InENP`, `lambda`, `mu` (`Statement.lean` §8);
`NearCubicWires.agreement` (uniform agreement on the cube).
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

open NearCubicWires NearCubicGates.Target

/-- The wire cap `⌊n⁴ / (K λ_n^{17/4} μ_n^{15/2})⌋` of `thm:main`. -/
noncomputable def wireCap (K n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ 4 / ((K : ℝ) * ((lambda n : ℕ) : ℝ) ^ ((17 : ℝ) / 4) * ((mu n : ℕ) : ℝ) ^ ((15 : ℝ) / 2))⌋₊

/-- The conclusion of `thm:main` at the gap `γ`. -/
def MainAt4 (gamma : ℚ) : Prop :=
  ∀ d : ℝ, 0 < d → d < (gamma : ℝ) / 5 →
    ∃ K : ℕ, 0 < K ∧ ∃ F : Language, NearCubicGates.Target.InENP F ∧
      ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
        ∀ C : SymmetricThresholdCircuit n,
          C.wireCount ≤ wireCap K n → NearCubicWires.agreement C.eval (F n) < 1 - d

/-- `thm:main`: some rational `γ ∈ (0, 1)` (the PCPP gap) satisfies `MainAt4`. -/
def MainStatement4 : Prop :=
  ∃ gamma : ℚ, 0 < gamma ∧ gamma < 1 ∧ MainAt4 gamma

/-- The working form of the final theorem: the base's published inputs imply `thm:main`. -/
def FinalStatement4' : Prop := NearCubicGates.Close.NineInputs → MainStatement4

end NearQuarticWires.Transfer
