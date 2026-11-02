import Proof.Quartic.Statement.Final
import Proof.Foundations.Semantics

/-!
# Bridges from `FinalStatement4`'s vocabulary to the proof's

Proof-side companions of `Proof/Quartic/Statement/Final.lean` (not part of the statement):

* `Budget4 K n w : (K·w)^4 · λ_n^17 · μ_n^30 ≤ n^16`, the integer form of the cap, and
  `le_wireCap_iff_budget4`: for `K > 0`, `n ≥ 4`, `w ≤ wireCap K n ↔ Budget4 K n w`. (Raise
  `K w λ^{17/4} μ^{15/2} ≤ n^4` to the fourth power; this is the size test of the paper's Lemma A.2 with
  the constant moved.)
* `A4 n = n^4/(λ_n^{17/4} μ_n^{15/2})` (paper/paper.tex, `𝒜₄(n)`) and `wireCap_eq_floor_A4`:
  `wireCap K n = ⌊𝒜₄(n)/K⌋₊`, the form used in the proof of `thm:main`.
* `fanIn_eq_support_card`, `wires_eq_wireCount`: the paper's `W(C) = G + Σ f_i` is the shared library's
  `SymmetricThresholdCircuit.wireCount = Σ_i (support.card + 1)` (`Proof/Foundations/Semantics.lean`).
* `agr_eq_agreement`: `agr C F` is the shared `NearCubicWires.agreement C.eval (F n)`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Statement

open NearCubicWires NearCubicGates.Target
open scoped BigOperators

/-- The integer form of the cap: `(K·w)^4 · λ_n^17 · μ_n^30 ≤ n^16`. -/
def Budget4 (K n w : ℕ) : Prop :=
  (K * w) ^ 4 * lambda n ^ 17 * mu n ^ 30 ≤ n ^ 16

instance (K n w : ℕ) : Decidable (Budget4 K n w) := Nat.decLe _ _

/-- `𝒜₄(n) = n^4 / (λ_n^{17/4} μ_n^{15/2})` (paper/paper.tex). -/
noncomputable def A4 (n : ℕ) : ℝ :=
  (n : ℝ) ^ 4 / ((lambda n : ℝ) ^ ((17 : ℝ) / 4) * (mu n : ℝ) ^ ((15 : ℝ) / 2))

/-- For `n ≥ 4`, `λ_n = ⌈log₂ n⌉ ≥ 2`. -/
theorem lambda_ge_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ lambda n := by
  have h4 : Nat.clog 2 4 = 2 := by norm_num
  calc 2 = Nat.clog 2 4 := h4.symm
    _ ≤ Nat.clog 2 n := Nat.clog_mono_right 2 hn

/-- For `n ≥ 4`, `μ_n = ⌈log₂ λ_n⌉ ≥ 1`. -/
theorem mu_ge_one {n : ℕ} (hn : 4 ≤ n) : 1 ≤ mu n := by
  have h2 : Nat.clog 2 2 = 1 := by norm_num
  calc 1 = Nat.clog 2 2 := h2.symm
    _ ≤ Nat.clog 2 (lambda n) := Nat.clog_mono_right 2 (lambda_ge_two hn)

/-- `wireCap K n = ⌊𝒜₄(n)/K⌋₊`. -/
theorem wireCap_eq_floor_A4 (K n : ℕ) : wireCap K n = ⌊A4 n / K⌋₊ := by
  unfold wireCap A4
  congr 1
  rw [div_div]
  congr 1
  ring

/-- **The cap in integers.** For `K > 0` and `n ≥ 4`, `w ≤ ⌊n^4/(K λ_n^{17/4} μ_n^{15/2})⌋` holds exactly
when `(K·w)^4 λ_n^17 μ_n^30 ≤ n^16`. -/
theorem le_wireCap_iff_budget4 {K n w : ℕ} (hK : 0 < K) (hn : 4 ≤ n) :
    w ≤ wireCap K n ↔ Budget4 K n w := by
  have hL : (0 : ℝ) < lambda n := by
    have := lambda_ge_two hn
    exact_mod_cast (show 0 < lambda n by omega)
  have hM : (0 : ℝ) < mu n := by
    have := mu_ge_one hn
    exact_mod_cast (show 0 < mu n by omega)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set Lr : ℝ := (lambda n : ℝ) ^ ((17 : ℝ) / 4) with hLr
  set Mr : ℝ := (mu n : ℝ) ^ ((15 : ℝ) / 2) with hMr
  have hLr0 : 0 < Lr := Real.rpow_pos_of_pos hL _
  have hMr0 : 0 < Mr := Real.rpow_pos_of_pos hM _
  have hLr4 : Lr ^ (4 : ℕ) = (lambda n : ℝ) ^ (17 : ℕ) := by
    rw [hLr, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hMr4 : Mr ^ (4 : ℕ) = (mu n : ℝ) ^ (30 : ℕ) := by
    rw [hMr, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    norm_num
  have hden : 0 < (K : ℝ) * Lr * Mr := by positivity
  unfold wireCap
  rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hden]
  have key : ((w : ℝ) * ((K : ℝ) * Lr * Mr)) ^ (4 : ℕ)
      = (((K * w) ^ 4 * lambda n ^ 17 * mu n ^ 30 : ℕ) : ℝ) := by
    push_cast
    rw [← hLr4, ← hMr4]
    ring
  have hn4 : ((n : ℝ) ^ 4) ^ (4 : ℕ) = ((n ^ 16 : ℕ) : ℝ) := by
    push_cast
    ring
  unfold Budget4
  rw [← Nat.cast_le (α := ℝ), ← key, ← hn4]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).symm

/-- The fan-in of Definition 1.1 is the size of the gate's retained support. -/
theorem fanIn_eq_support_card {n : ℕ} (T : RealThresholdGate n) : fanIn T = T.support.card := by
  unfold fanIn
  congr 1
  ext l
  simp [T.mem_support_iff l]

/-- The paper's wire count `W(C) = G + Σ_i f_i` is the shared library's `wireCount = Σ_i (f_i + 1)`. -/
theorem wires_eq_wireCount {n : ℕ} (C : SymmetricThresholdCircuit n) : wires C = C.wireCount := by
  unfold wires SymmetricThresholdCircuit.wireCount
  rw [Finset.sum_add_distrib]
  simp [fanIn_eq_support_card, add_comm]

/-- `agr` is the shared library's uniform agreement of `C.eval` with `F` at length `n`. -/
theorem agr_eq_agreement {n : ℕ} (C : SymmetricThresholdCircuit n) (F : Language) :
    agr C F = NearCubicWires.agreement C.eval (F n) := rfl

end NearQuarticWires.Statement
