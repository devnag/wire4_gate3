import Proof.Quartic.Transfer.Statement4
import Proof.Gates.HeadlineAssembly
import Proof.Gates.Transfer.Budget
import Proof.Foundations.CircuitRestriction

/-!
# Every sufficiently large length (paper §A.6, `prop:ae-final`)

From a native family that is hard for `SYM∘THR` circuits with at most `𝒜₄(q)/D` wires (`NativeFrontier4.hard`), the
padded language is hard at every large length `n` for circuits with at most `⌊𝒜₄(n)/K⌋` wires, `K = D·B⁴`:
* *Restriction* (`lem:ae-wires` (b),(c)): fixing the ignored inputs of `C` to an averaging-optimal assignment gives a
  circuit on the native inputs with no more wires (`exists_wire_restriction`);
* *Cap* (`lem:ae-cap` (v)): `𝒜₄(n) ≤ (n/q)⁴ 𝒜₄(q) ≤ B⁴ 𝒜₄(q)` for `q ≤ n ≤ B q` (`A4_dilation`).
This is the base's `HeadlineAssembly` with the wire count in place of top weight and `𝒜₄` in place of `𝒜₃`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

open scoped BigOperators
open NearCubicWires NearCubicGates.Target NearCubicWires.CircuitRestriction NearCubicWires.RecoveryPipeline
open NearCubicWires.ComponentwiseTransfer

theorem lambda_pos {q : ℕ} (hq : 4 ≤ q) : (0 : ℝ) < ((lambda q : ℕ) : ℝ) := by
  have := NearCubicGates.Close.Transfer.lambda_ge_two hq
  exact_mod_cast (show 0 < lambda q by omega)

theorem mu_pos {q : ℕ} (hq : 4 ≤ q) : (0 : ℝ) < ((mu q : ℕ) : ℝ) := by
  have := NearCubicGates.Close.Transfer.mu_ge_one hq
  exact_mod_cast (show 0 < mu q by omega)

/-- The logarithmic denominator `λ^{17/4} μ^{15/2}` of `𝒜₄`. -/
noncomputable def logDen (n : ℕ) : ℝ :=
  ((lambda n : ℕ) : ℝ) ^ ((17 : ℝ) / 4) * ((mu n : ℕ) : ℝ) ^ ((15 : ℝ) / 2)

theorem A4_eq (n : ℕ) : A4 n = (n : ℝ) ^ 4 / logDen n := by
  unfold A4 logDen; rfl

theorem logDen_pos {q : ℕ} (hq : 4 ≤ q) : 0 < logDen q :=
  mul_pos (Real.rpow_pos_of_pos (lambda_pos hq) _) (Real.rpow_pos_of_pos (mu_pos hq) _)

theorem logDen_mono {q n : ℕ} (hq : 4 ≤ q) (hqn : q ≤ n) : logDen q ≤ logDen n := by
  unfold logDen
  have hl : ((lambda q : ℕ) : ℝ) ≤ ((lambda n : ℕ) : ℝ) := by
    exact_mod_cast NearCubicGates.Close.Transfer.lambda_mono hqn
  have hm : ((mu q : ℕ) : ℝ) ≤ ((mu n : ℕ) : ℝ) := by
    exact_mod_cast NearCubicGates.Close.Transfer.mu_mono hqn
  exact mul_le_mul (Real.rpow_le_rpow (lambda_pos hq).le hl (by norm_num))
    (Real.rpow_le_rpow (mu_pos hq).le hm (by norm_num)) (Real.rpow_pos_of_pos (mu_pos hq) _).le
    (Real.rpow_nonneg (by positivity) _)

theorem A4_nonneg (n : ℕ) : 0 ≤ A4 n := by
  unfold A4
  exact div_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _))

/-- `lem:ae-cap` (v), in the form used: `𝒜₄(n) ≤ B⁴ 𝒜₄(q)` when `4 ≤ q ≤ n ≤ B q` (`λ`, `μ` nondecreasing). -/
theorem A4_dilation {q n B : ℕ} (hq : 4 ≤ q) (hqn : q ≤ n) (hnB : n ≤ B * q) :
    A4 n ≤ (B : ℝ) ^ 4 * A4 q := by
  rw [A4_eq, A4_eq]
  have hXq := logDen_pos hq
  have hXqn := logDen_mono hq hqn
  have hn4 : (n : ℝ) ^ 4 ≤ (B : ℝ) ^ 4 * (q : ℝ) ^ 4 := by
    have : (n : ℝ) ≤ B * q := by exact_mod_cast hnB
    calc (n : ℝ) ^ 4 ≤ ((B : ℝ) * q) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
      _ = _ := by ring
  calc (n : ℝ) ^ 4 / logDen n ≤ (n : ℝ) ^ 4 / logDen q := div_le_div_of_nonneg_left (by positivity) hXq hXqn
    _ ≤ (B : ℝ) ^ 4 * (q : ℝ) ^ 4 / logDen q := div_le_div_of_nonneg_right hn4 hXq.le
    _ = (B : ℝ) ^ 4 * ((q : ℝ) ^ 4 / logDen q) := by ring

/-- The floor cap of `thm:main` is at most `𝒜₄(n)/K`. -/
theorem wireCap_le (K n : ℕ) : (wireCap K n : ℝ) ≤ A4 n / K := by
  unfold wireCap
  have hx : (0 : ℝ) ≤ (n : ℝ) ^ 4 / ((K : ℝ) * ((lambda n : ℕ) : ℝ) ^ ((17 : ℝ) / 4) *
      ((mu n : ℕ) : ℝ) ^ ((15 : ℝ) / 2)) :=
    div_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _))
  refine (Nat.floor_le hx).trans (le_of_eq ?_)
  unfold A4
  rw [div_div, mul_assoc, mul_comm]

/-- The padded language at length `n` is the core function padded by its ignored suffix. -/
theorem padded_eq_padCore (q : ℕ → ℕ) (hq : ∀ n, q n ≤ n) (native : (n : ℕ) → BoolFunction (q n)) (n : ℕ) :
    NearCubicGates.HeadlineAssembly.padded q hq native n = padCore (native n) (hq n) := by
  funext x
  simp only [NearCubicGates.HeadlineAssembly.padded, padCore]
  congr 1

/-- `lem:ae-wires` (b),(c): some literal restriction of `C` to the core inputs has no more wires and at least the padded
agreement. -/
theorem exists_wire_restriction {m n : ℕ} (h : m ≤ n) (C : SymmetricThresholdCircuit n) (f : BoolFunction m) :
    ∃ small : SymmetricThresholdCircuit m, small.wireCount ≤ C.wireCount ∧
      NearCubicWires.agreement C.eval (padCore f h) ≤ NearCubicWires.agreement small.eval f := by
  classical
  have hE := agreement_padCore_eq_expect_restrictions C.eval f h
  obtain ⟨p, -, hp⟩ := Finset.exists_le_of_le_expect (s := (Finset.univ : Finset (BitInput (n - m))))
    Finset.univ_nonempty (le_of_eq hE)
  refine ⟨restrictSymmetricCircuit C h p, restrictSymmetricCircuit_wireCount_le C h p, ?_⟩
  have hev : (restrictSymmetricCircuit C h p).eval = restrictTarget C.eval h p :=
    funext (restrictSymmetricCircuit_eval C h p)
  rw [hev]
  exact hp

/-- A native family hard below the wire cap `𝒜₄(q)/D` at its own length, with the length schedule and the `E^NP`
recovery of its padding (the base's `HeadlineAssembly.NativeFrontier` for wires). -/
structure NativeFrontier4 (γ ε : ℝ) where
  q : ℕ → ℕ
  q_le : ∀ n, q n ≤ n
  native : (n : ℕ) → BoolFunction (q n)
  budgetConstant : ℕ
  budgetPositive : 0 < budgetConstant
  dilation : ℕ
  dilationPositive : 0 < dilation
  onset : ℕ
  lengthBound : ∀ n, onset ≤ n → n ≤ dilation * q n
  hard : ∀ n, onset ≤ n → ∀ C : SymmetricThresholdCircuit (q n),
    (C.wireCount : ℝ) ≤ A4 (q n) / budgetConstant →
      NearCubicWires.agreement C.eval (native n) < 1 - γ / 5 + ε
  ordinaryRecovery : NearCubicGates.Target.InENP (NearCubicGates.HeadlineAssembly.padded q q_le native)

/-- `prop:ae-final`, cap and restriction steps: `K = D B⁴`. -/
theorem padded_hardness4 (q : ℕ → ℕ) (hq : ∀ n, q n ≤ n) (native : (n : ℕ) → BoolFunction (q n))
    (D B onset : ℕ) (hD : 0 < D) (hB : 0 < B) (hdilate : ∀ n, onset ≤ n → n ≤ B * q n) (d : ℝ)
    (hnative : ∀ n, onset ≤ n → ∀ C : SymmetricThresholdCircuit (q n),
      (C.wireCount : ℝ) ≤ A4 (q n) / D → NearCubicWires.agreement C.eval (native n) < 1 - d) :
    ∃ K : ℕ, 0 < K ∧ ∀ n, max onset (4 * B) ≤ n → ∀ C : SymmetricThresholdCircuit n,
      C.wireCount ≤ wireCap K n →
        NearCubicWires.agreement C.eval (NearCubicGates.HeadlineAssembly.padded q hq native n) < 1 - d := by
  refine ⟨D * B ^ 4, by positivity, ?_⟩
  intro n hn C hC
  have hon : onset ≤ n := le_trans (le_max_left _ _) hn
  have h4B : 4 * B ≤ n := le_trans (le_max_right _ _) hn
  have hdil := hdilate n hon
  have hq4 : 4 ≤ q n := Nat.le_of_mul_le_mul_left (by rw [mul_comm B 4]; exact h4B.trans hdil) hB
  obtain ⟨small, hw, ha⟩ := exists_wire_restriction (hq n) C (native n)
  rw [padded_eq_padCore]
  refine lt_of_le_of_lt ha (hnative n hon small ?_)
  have h1 : (small.wireCount : ℝ) ≤ (wireCap (D * B ^ 4) n : ℝ) := by exact_mod_cast hw.trans hC
  have h2 := wireCap_le (D * B ^ 4) n
  have h3 : A4 n ≤ (B : ℝ) ^ 4 * A4 (q n) := A4_dilation hq4 (hq n) hdil
  have hDB : (0 : ℝ) < ((D * B ^ 4 : ℕ) : ℝ) := by positivity
  have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  calc (small.wireCount : ℝ) ≤ A4 n / ((D * B ^ 4 : ℕ) : ℝ) := h1.trans h2
    _ ≤ (B : ℝ) ^ 4 * A4 (q n) / ((D * B ^ 4 : ℕ) : ℝ) := div_le_div_of_nonneg_right h3 hDB.le
    _ = A4 (q n) / D := by push_cast; field_simp

theorem mainAt4_of_native_frontier4 (γ : ℚ) (hγ : 0 < γ)
    (hfrontier : ∀ ε : ℝ, 0 < ε → ε < (γ : ℝ) / 5 → Nonempty (NativeFrontier4 γ ε)) : MainAt4 γ := by
  intro d hd hdγ
  let ε : ℝ := ((γ : ℝ) / 5 - d) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεγ : ε < (γ : ℝ) / 5 := by
    have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ
    dsimp [ε]
    linarith
  obtain ⟨F⟩ := hfrontier ε hε hεγ
  have hn : ∀ n, F.onset ≤ n → ∀ C : SymmetricThresholdCircuit (F.q n),
      (C.wireCount : ℝ) ≤ A4 (F.q n) / F.budgetConstant →
        NearCubicWires.agreement C.eval (F.native n) < 1 - d := by
    intro n hn C hC
    have h := F.hard n hn C hC
    dsimp [ε] at h
    linarith
  obtain ⟨K, hK, hhard⟩ := padded_hardness4 F.q F.q_le F.native F.budgetConstant F.dilation F.onset
    F.budgetPositive F.dilationPositive F.lengthBound d hn
  refine ⟨K, hK, NearCubicGates.HeadlineAssembly.padded F.q F.q_le F.native, F.ordinaryRecovery,
    max 4 (max F.onset (4 * F.dilation)), le_max_left _ _, ?_⟩
  intro n hN
  exact hhard n (le_trans (le_max_right _ _) hN)

theorem mainStatement4_of_native_frontier4 (γ : ℚ) (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hfrontier : ∀ ε : ℝ, 0 < ε → ε < (γ : ℝ) / 5 → Nonempty (NativeFrontier4 γ ε)) : MainStatement4 :=
  ⟨γ, hγ, hγ₁, mainAt4_of_native_frontier4 γ hγ hfrontier⟩

end NearQuarticWires.Transfer
