import Statement

/-!
# The main theorem: `FinalStatement4` (`thm:main`, Theorem 1.1)

`FinalStatement4` states `thm:main` of the joint paper, paper/paper.tex:

> Let 0<γ<1 be a fixed absolute constant: the rational rejection gap of the three-query PCP of proximity of Chen
> and Williams [CW19, Lemma 24] (`imp:transfer-pcpp`). For every fixed 0<d<γ/5 there are a positive
> integer K_d, a language F_d ∈ E^NP, and an integer n_0 ≥ 4 such that, for every n ≥ n_0 and every SYM∘THR
> circuit C on n inputs,
>   W(C) ≤ ⌊n^4/(K_d λ_n^{17/4} μ_n^{15/2})⌋  ⟹  agr(C, F_d) < 1 − d.

in the vocabulary of `def:class` (Definition 1.1) and of the paragraph after it (λ_n, μ_n, 𝒜₄, agr).
`SourceMapping/main-theorem.md` quotes each of these passages beside its Lean declaration.

## Where each definition lives

* `Statement.lean`: `NearCubicWires.BitInput`, `Language`, `RealThresholdGate` (with `eval` and
  `bitAsReal`), `NearCubicGates.Target.lambda`, `mu`, `InENP` (with its E^NP certificate).
* This file: the circuit class `NearCubicWires.SymmetricThresholdCircuit` and its `eval`, and (namespace
  `NearQuarticWires.Statement`) `fanIn`, `wires`, `agr`, `wireCap`, `MainAt4`, `FinalStatement4`. It imports
  `Statement.lean` only; `SourceMapping/main-theorem.md` prints every declaration of the closure of the release
  statement.

No proof is in this file.
-/

set_option autoImplicit false

namespace NearCubicWires

/-- A `SYM∘THR` circuit (`def:class`): `bottomCount = G` occurrences of real threshold gates (repetitions are
separate indices of `bottom`) and a lookup `top` read at the number of occurrences that output one. -/
structure SymmetricThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  top : ℕ → Bool

/-- The value `C(x) = g(Σ_i T_i(x))` (`def:class`): the lookup at the number of occurrences that output one. -/
noncomputable def SymmetricThresholdCircuit.eval {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) (input : BitInput n) : Bool :=
  circuit.top ((Finset.univ.filter fun i => (circuit.bottom i).eval input).card)

end NearCubicWires

namespace NearQuarticWires.Statement

open NearCubicWires NearCubicGates.Target
open scoped BigOperators

/-- The fan-in `f_i` of an occurrence `T_i` (`def:class`): "Let `f_i` be the number of
inputs `l` with `w_{i,l} ≠ 0`, the *fan-in* of `T_i`." -/
noncomputable def fanIn {n : ℕ} (T : RealThresholdGate n) : ℕ :=
  (Finset.univ.filter fun l : Fin n => T.weight l ≠ 0).card

/-- The wire count (`def:class`): `W(C) = G + Σ_{i=1}^G f_i`, "the top fan-in plus the
total bottom fan-in". `G = C.bottomCount` is the number of occurrences; repeated occurrences are separate
indices of `C.bottom` and are counted separately. -/
noncomputable def wires {n : ℕ} (C : SymmetricThresholdCircuit n) : ℕ :=
  C.bottomCount + ∑ i : Fin C.bottomCount, fanIn (C.bottom i)

/-- `agr(C, F) = Pr_{x ∈ {0,1}^n}[C(x) = F(x)]` (after `def:class`), uniform over the `2^n` inputs; `F n` is
the language at length `n`. Same formula as `NearCubicGates.Target.agreement`, for SYM∘THR circuits. -/
noncomputable def agr {n : ℕ} (C : SymmetricThresholdCircuit n) (F : Language) : ℝ :=
  ((Finset.univ.filter fun x : BitInput n => C.eval x = F n x).card : ℝ) /
    (Fintype.card (BitInput n) : ℝ)

/-- The boxed cap of `thm:main`, literally: `⌊n^4 / (K λ_n^{17/4} μ_n^{15/2})⌋`, with
`λ_n = ⌈log₂ n⌉ = lambda n` and `μ_n = ⌈log₂ λ_n⌉ = mu n` (after `def:class`), real powers, and the floor
taken in `ℕ` (the argument is `≥ 0`). For `n ≥ 4`, `K > 0` it equals `⌊𝒜₄(n)/K⌋` and is equivalent to the
integer test `(K·w)^4 λ^17 μ^30 ≤ n^16` (`Proof/Quartic/Statement/Budget.lean`). -/
noncomputable def wireCap (K n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ 4 /
      ((K : ℝ) * (lambda n : ℝ) ^ ((17 : ℝ) / 4) * (mu n : ℝ) ^ ((15 : ℝ) / 2))⌋₊

/-- The conclusion of `thm:main` for a fixed rational `γ` : for every fixed `0 < d < γ/5`
there are a positive integer `K_d`, a language `F_d ∈ E^NP` and an integer `n₀ ≥ 4` (`λ_n`, `μ_n` are defined
for `n ≥ 4`) such that for every `n ≥ n₀` and every SYM∘THR circuit
`C` on `n` inputs, `W(C) ≤ ⌊n^4/(K_d λ_n^{17/4} μ_n^{15/2})⌋ ⟹ agr(C, F_d) < 1 − d`. -/
def MainAt4 (gamma : ℚ) : Prop :=
  ∀ d : ℝ, 0 < d → d < (gamma : ℝ) / 5 →
    ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
      ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
        ∀ C : SymmetricThresholdCircuit n,
          wires C ≤ wireCap K n → agr C F < 1 - d

/-- **The main theorem** (`thm:main`, Theorem 1.1). The paper's `γ` is the fixed rational
rejection gap of the three-query proof system (`imp:transfer-pcpp`); it is quantified here as in the near-cubic
gate theorem's statement `NearCubicGates.Target.MainStatement`: some rational `γ` with `0 < γ < 1`. -/
def FinalStatement4 : Prop :=
  ∃ gamma : ℚ, 0 < gamma ∧ gamma < 1 ∧ MainAt4 gamma

end NearQuarticWires.Statement
