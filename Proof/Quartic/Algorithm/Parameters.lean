import Proof.Gates.RationalRateChain
import Proof.Gates.ScalarWindow
import Proof.Gates.TomographyDirections

/-!
# Parameters with exact finite rules, and the witness

Paper: `sec:params`, paper/paper.tex, and the witness.

All choices depend only on `(n, β, W, G_1, G_2)` and on whether the call is a pair call, never on the witness.
Floors and ceilings of expressions with square roots or `m`th roots are computed exactly by comparing integer powers
(`ceilSqrt`, and the fourth-power comparison defining `Q`); all other comparisons are exact rational comparisons.
If `n < 4` the algorithm returns the sound default; if `W = 0` the call is evaluated exactly; if a requirement
fails, the algorithm returns the sound default.
-/

set_option autoImplicit false

namespace NearQuarticWires.Algorithm

/-- The data of a normalized call that the parameters read (`sec:params`, paper/paper.tex):
the input length `n`, the radius `β`, the total wire count `W`, the occurrence counts `G_1`, `G_2`, and whether the
call is a pair call (`𝒥 = {1, 2}`). -/
structure CallShape where
  n : ℕ
  β : ℚ
  W : ℕ
  G₁ : ℕ
  G₂ : ℕ
  pair : Bool

/-- The least natural number `u` with `u² ≥ a`, by integer comparison (`sec:params`, paper/paper.tex). -/
def ceilSqrt (a : ℕ) : ℕ := if a = 0 then 0 else Nat.sqrt (a - 1) + 1

/-- `sec:params` item 6, paper/paper.tex: `e_P`, the least `e ≥ 1` with `(P/2)^e ≥ 2^{B_N}`,
i.e. `P^e ≥ 2^{B_N + e}`. For `P ≥ 4` it is at most `max 1 B_N`, so a search over `[0, max 1 B_N]` finds it. -/
def primeExponent (BN P : ℕ) : ℕ :=
  ((List.range (max 1 BN + 1)).find? (fun e => 1 ≤ e ∧ 2 ^ (BN + e) ≤ P ^ e)).getD (max 1 BN)

/-- `imp:window`(b), paper/paper.tex: `L_2`, the largest `L ≥ 2` with
`S_φ(⌊(D' - 1)/(L - 1)⌋) ≥ L`, or `1` if there is none. Every such `L` is at most `D'`. -/
def pairWindow (Dprime : ℕ) : ℕ :=
  let L := Nat.findGreatest
    (fun L => 2 ≤ L ∧ L ≤ NearCubicGates.TomographyDirections.degreeSum ((Dprime - 1) / (L - 1))) Dprime
  if L = 0 then 1 else L

/-- The parameters of `sec:params`, paper/paper.tex, in the paper's notation. The chain of
`imp:chain` is recorded by `J`, the multipliers `rate i = a_{i+1}` for `i < J - 1`, `M_1` and `A = Π a_i`. -/
structure Parameters where
  lam : ℕ
  mu : ℕ
  m : ℕ
  r : ℕ
  s : ℕ
  b : ℕ
  k : ℕ
  N : ℕ
  Jmax : ℕ
  T : ℕ
  tau : ℕ
  U : ℕ
  pi0 : ℚ
  Xmax : ℕ
  dstar : ℕ
  Omega₁ : ℕ
  Omega₂ : ℕ
  Theta : ℕ
  I : ℕ
  MF : ℕ
  eta : ℚ
  Q : ℕ
  lf : ℕ
  S : ℕ
  Nat_ : ℕ
  mc : ℕ
  Uocc : ℕ
  Dmax : ℕ
  BN : ℕ
  P : ℕ
  e : ℕ
  primes : Finset ℕ
  Dprime : ℕ
  L2 : ℕ
  Lw : ℕ
  hE : ℕ
  h : ℕ
  ell0 : ℕ
  ellBar : ℚ
  M1 : ℕ
  J : ℕ
  rate : ℕ → ℕ
  A : ℕ
  Lambda : ℕ
  /-- `η > 0` (`sec:params` item 4). -/
  eta_pos : 0 < eta
  /-- The rule for `Q` (item 4), raised to the fourth power: `4096⁴ · 4 · I · N⁶ ≤ Q⁴ η⁸`. -/
  budget : (4096 : ℚ) ^ 4 * 4 * I * (N : ℚ) ^ 6 ≤ (Q : ℚ) ^ 4 * eta ^ 8
  /-- `𝒫` consists of primes and is nonempty (item 6). -/
  primes_prime : ∀ p ∈ primes, p.Prime
  primes_nonempty : primes.Nonempty
  /-- `2h_E ≤ p + 1` for every `p ∈ 𝒫`, from `h_E = ⌊P/4⌋` and `p > P/2` (used in `lem:certify`(c)). -/
  width : ∀ p ∈ primes, 2 * hE ≤ p + 1
  Dprime_eq : Dprime = NearCubicGates.ScalarWindow.window primes
  L2_eq : L2 = pairWindow Dprime
  /-- `Λ = ⌊(L_w - 1)A/2⌋ + 1` (item 7), hence `2Λ ≤ (L_w - 1)A + 2` (used in `lem:certify`(d)). -/
  Lambda_eq : Lambda = (Lw - 1) * A / 2 + 1
  box : 2 * Lambda ≤ (Lw - 1) * A + 2
  /-- The rules of items 1, 4 and 6 that the modulus bound of `lem:residue` reads. -/
  m_eq : m = 4
  k_even : k % 2 = 0
  N_eq : N = 2 ^ (k / 2)
  S_eq : S = 2 * m * lf
  BN_eq : BN = S + m * k + 2 * m * Nat.clog 2 (N ^ 2 * Q) + 1
  P_ge : 100 ≤ P
  e_eq : e = primeExponent BN P
  primes_gt : ∀ p ∈ primes, P < 2 * p
  /-- Whether the call is a pair call, and `L_w = L_2` for a pair call, `L_w = D'` otherwise (item 6). -/
  pair : Bool
  Lw_eq : Lw = if pair then L2 else Dprime
  /-- `A = Π_{i<J} a_i > 0`: every multiplier of the chain is positive (`imp:chain`(i)). -/
  A_pos : 0 < A

/-- The three outcomes of the parameter rules (`sec:params`, paper/paper.tex). -/
inductive Plan
  /-- `n < 4` or a requirement fails: return `(1/2, 1/2)`. -/
  | soundDefault
  /-- `W = 0`: the circuits are constant and the call is evaluated exactly. -/
  | exactEvaluation
  /-- Run Steps 1–5 with these parameters. -/
  | run (P : Parameters)

/-- A requirement whose proof the following rules use: `some` of a proof, or `none` if it fails. -/
def require (p : Prop) [Decidable p] : Option (PLift p) := if h : p then some ⟨h⟩ else none

theorem ceilSqrt_pos (a : ℕ) (ha : 0 < a) : 0 < ceilSqrt a := by
  unfold ceilSqrt
  split_ifs <;> omega

/-- `sec:params` item 4: the least power of two `Q = 2^{t_Q}` with `Q⁴ η⁸ ≥ (1024 N m)⁴ · 4N²I` (`m = 4`) satisfies
`4096⁴ · 4 · I · N⁶ ≤ Q⁴ η⁸`. -/
theorem sampleBudget_le (N I : ℕ) (η : ℚ) (hη : 0 < η) :
    (4096 : ℚ) ^ 4 * 4 * I * (N : ℚ) ^ 6 ≤
      (((2 ^ ((Nat.clog 2 ⌈((1024 : ℚ) * N * (4 : ℕ)) ^ 4 * (4 * (N : ℚ) ^ 2 * I) / η ^ 8⌉₊ + 3) / 4) : ℕ) :
        ℚ)) ^ 4 * η ^ 8 := by
  set y : ℚ := ((1024 : ℚ) * N * (4 : ℕ)) ^ 4 * (4 * (N : ℚ) ^ 2 * I) / η ^ 8 with hy
  set c := Nat.clog 2 ⌈y⌉₊
  have h1 : y ≤ (⌈y⌉₊ : ℚ) := Nat.le_ceil y
  have h2 : ⌈y⌉₊ ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have h3 : 2 ^ c ≤ (2 ^ ((c + 3) / 4)) ^ 4 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : y ≤ (((2 ^ ((c + 3) / 4) : ℕ) : ℚ)) ^ 4 := by
    have : ((⌈y⌉₊ : ℕ) : ℚ) ≤ (((2 ^ ((c + 3) / 4)) ^ 4 : ℕ) : ℚ) := by exact_mod_cast h2.trans h3
    push_cast at this ⊢
    linarith
  have hη8 : (0 : ℚ) < η ^ 8 := by positivity
  have h5 := mul_le_mul_of_nonneg_right h4 hη8.le
  rw [hy, div_mul_cancel₀ _ hη8.ne'] at h5
  calc (4096 : ℚ) ^ 4 * 4 * I * (N : ℚ) ^ 6 = ((1024 : ℚ) * N * (4 : ℕ)) ^ 4 * (4 * (N : ℚ) ^ 2 * I) := by
        push_cast; ring
    _ ≤ _ := h5

/-- `imp:chain`(i): a multiplier `a = max{a : 16a²x ≤ 1}` of a stage with `0 < x < 2^{-8}` is positive. -/
theorem factorRat_pos (x : ℚ) (hx : 0 < x) (hsmall : x < 1 / 256) :
    0 < NearCubicGates.RationalRateChain.factorRat x := by
  unfold NearCubicGates.RationalRateChain.factorRat
  apply Nat.lt_of_lt_of_le Nat.zero_lt_one
  apply Nat.le_findGreatest
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))
  · push_cast
    linarith

/-- `imp:chain`(i): the product `A` of the multipliers of the stages before the first stage with `x ≥ 2^{-8}` is
positive. -/
theorem prod_factorRat_pos (x1 : ℚ) (hx1 : 0 < x1) (j0 : ℕ)
    (hstop : ∀ i < j0, ¬ (1 / 256 ≤ NearCubicGates.RationalRateChain.ratio x1 i)) :
    0 < ∏ i ∈ Finset.range j0,
      NearCubicGates.RationalRateChain.factorRat (NearCubicGates.RationalRateChain.ratio x1 i) := by
  apply Finset.prod_pos
  intro i hi
  have hpos : 0 < NearCubicGates.RationalRateChain.ratio x1 i := by
    have h := NearCubicGates.NestedRateChain.ratio_positive (x1 : ℝ) (by exact_mod_cast hx1) i
    rw [← NearCubicGates.RationalRateChain.ratio_cast x1 hx1 i] at h
    exact_mod_cast h
  exact factorRat_pos _ hpos (lt_of_not_ge (hstop i (Finset.mem_range.mp hi)))

/-- **The parameter rules** of `sec:params`, paper/paper.tex, for `n ≥ 4` and `W > 0`. The result is
`none` exactly when a requirement fails. -/
def parameters (c : CallShape) : Option Parameters := do
  let n := c.n
  let β := c.β
  -- normalized calls have `β ≥ n^{-B_1} > 0` (`sec:counting`)
  let ⟨hβ⟩ ← require (0 < β)
  -- item 1
  let lam : ℕ := Nat.clog 2 n
  let mu : ℕ := Nat.clog 2 lam
  let m : ℕ := 4
  let r : ℕ := 16 * mu
  guard (4 * r ≤ n)
  let s : ℕ := Nat.log 2 ((n + r) / r)
  let b : ℕ := 2 ^ s - 1
  let k : ℕ := r * s
  let N : ℕ := 2 ^ (k / 2)
  -- item 2
  let Jmax : ℕ := mu + 1
  let T : ℕ := max 1 (Nat.clog 2 ⌈(2 : ℚ) ^ (m * k + 2 * m + 5) * Jmax / β⌉₊)
  -- item 3
  let tau : ℕ := k + Nat.clog 2 ⌈16 / β⌉₊
  let U : ℕ := max tau (ceilSqrt ⌈((96 : ℚ) * c.W / β) ^ 2 * (r : ℚ) ^ 3 / (n : ℚ) ^ 3⌉₊)
  let pi0 : ℚ := tau / (4 * U)
  let Xmax : ℕ := ceilSqrt (9 * tau ^ 2 * n * r)
  let dstar : ℕ := (2 * Xmax * U) / (3 * r * tau)
  -- item 4
  let Omega₁ : ℕ := 4 * m * c.G₁ + 1
  let Omega₂ : ℕ := if c.pair then 4 * m * c.G₂ + 1 else 1
  let Theta : ℕ := Omega₁ * Omega₂
  let I : ℕ := 2 * Theta
  let MF : ℕ := ceilSqrt Theta
  let eta : ℚ := β / (16 * MF)
  let tQ : ℕ := (Nat.clog 2 ⌈((1024 : ℚ) * N * m) ^ 4 * (4 * (N : ℚ) ^ 2 * I) / eta ^ 8⌉₊ + 3) / 4
  let Q : ℕ := 2 ^ tQ
  let lf : ℕ := max k (Nat.log 2 Q + 1)
  let S : ℕ := 2 * m * lf
  -- item 5
  let B0 : ℕ := 4 * n * Nat.clog 2 (n + 1)
  let Nat_ : ℕ := (4 * m + 1) * 2 * n ^ 4
  let mc : ℕ := n * (B0 + lam + 3)
  let Uocc : ℕ := 1 + Nat_ * mc
  guard (k ≤ n ∧ 100 * (m * k + 2) ≤ n - k)
  let Dmax : ℕ := (n - k - 100 * (m * k + 2)) / (100 * Nat.clog 2 Uocc)
  -- item 6
  let BN : ℕ := S + m * k + 2 * m * Nat.clog 2 (N ^ 2 * Q) + 1
  let P : ℕ := Nat.findGreatest (fun P => 100 ≤ P ∧
    (2 * primeExponent BN P - 1) * (2 * Jmax + 2) * (P - 1) + 4 * m * Xmax ≤ Dmax) n
  let ⟨hP⟩ ← require (100 ≤ P)
  let e : ℕ := primeExponent BN P
  guard (4 * m * Xmax + 2 * m * k ≤ Dmax)
  let primes := (Finset.range (P + 1)).filter (fun p => P < 2 * p ∧ p.Prime)
  let ⟨hne⟩ ← require primes.Nonempty
  let Dprime : ℕ := NearCubicGates.ScalarWindow.window primes
  let L2 : ℕ := pairWindow Dprime
  let Lw : ℕ := if c.pair then L2 else Dprime
  -- item 7
  let hE : ℕ := P / 4
  let h : ℕ := hE / (2 * m)
  let ⟨hTh⟩ ← require (64 * T ≤ h)
  let ell0 : ℕ := 32 * m * U
  let ellBar : ℚ := max (ell0 : ℚ) ((h : ℚ) ^ 2 / (256 * T))
  let piStar : ℚ := (h : ℚ) ^ 2 / (8 * T * ellBar)
  let M1 : ℕ := ⌈4 * ellBar / h⌉₊
  let x1 : ℚ := (1 / (M1 : ℚ)) / piStar
  -- `J` is the first stage with `x_J ≥ 2^{-8}`; it must satisfy `J ≤ J_max` (item 7)
  let ⟨hstopEx⟩ ← require (∃ j, j < Jmax ∧ 1 / 256 ≤ NearCubicGates.RationalRateChain.ratio x1 j)
  let j0 : ℕ := Nat.find hstopEx
  let J : ℕ := j0 + 1
  let rate := fun i => NearCubicGates.RationalRateChain.factorRat (NearCubicGates.RationalRateChain.ratio x1 i)
  let A : ℕ := ∏ i ∈ Finset.range (J - 1), rate i
  let Lambda : ℕ := (Lw - 1) * A / 2 + 1
  have hΩ₂ : 0 < Omega₂ := by
    show 0 < (if c.pair = true then 4 * m * c.G₂ + 1 else 1)
    split_ifs <;> omega
  have hMF : 0 < MF := ceilSqrt_pos _ (Nat.mul_pos (by omega) hΩ₂)
  have heta : 0 < eta := div_pos hβ (by positivity)
  return ⟨lam, mu, m, r, s, b, k, N, Jmax, T, tau, U, pi0, Xmax, dstar, Omega₁, Omega₂, Theta, I, MF, eta,
    Q, lf, S, Nat_, mc, Uocc, Dmax, BN, P, e, primes, Dprime, L2, Lw, hE, h, ell0, ellBar, M1, J, rate, A,
    Lambda, heta, sampleBudget_le N I eta heta, fun p hp => (Finset.mem_filter.mp hp).2.2, hne,
    fun p hp => by have := (Finset.mem_filter.mp hp).2.1; omega, rfl, rfl, rfl, by omega, rfl,
    by show 16 * mu * s % 2 = 0; rw [show 16 * mu * s = 2 * (8 * mu * s) by ring]; exact Nat.mul_mod_right 2 _,
    rfl, rfl, rfl, hP, rfl, fun p hp => (Finset.mem_filter.mp hp).2.1, c.pair, rfl,
    by
      have hT : 1 ≤ T := le_max_left _ _
      have hh : (0 : ℚ) < h := by exact_mod_cast (show 0 < h by omega)
      have hTq : (0 : ℚ) < T := by exact_mod_cast (show 0 < T by omega)
      have hbar : 0 < ellBar := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      have hM1 : (0 : ℚ) < M1 := by
        have : 0 < M1 := Nat.ceil_pos.mpr (by positivity)
        exact_mod_cast this
      have hx1 : 0 < x1 := by
        show 0 < (1 / (M1 : ℚ)) / ((h : ℚ) ^ 2 / (8 * T * ellBar))
        positivity
      show 0 < ∏ i ∈ Finset.range (j0 + 1 - 1), rate i
      rw [Nat.add_sub_cancel]
      exact prod_factorRat_pos x1 hx1 j0 fun i hi h =>
        Nat.find_min hstopEx hi ⟨lt_trans hi (Nat.find_spec hstopEx).1, h⟩⟩

/-- `sec:params` item 6: for `P ≥ 4`, `e_P` satisfies `e_P ≥ 1` and `(P/2)^{e_P} ≥ 2^{B_N}`, i.e.
`2^{B_N + e_P} ≤ P^{e_P}`. -/
theorem primeExponent_spec (BN P : ℕ) (hP : 4 ≤ P) :
    1 ≤ primeExponent BN P ∧ 2 ^ (BN + primeExponent BN P) ≤ P ^ primeExponent BN P := by
  unfold primeExponent
  cases h : (List.range (max 1 BN + 1)).find? (fun e => decide (1 ≤ e ∧ 2 ^ (BN + e) ≤ P ^ e)) with
  | some e =>
    have := List.find?_some h
    simpa using this
  | none =>
    simp only [Option.getD_none]
    refine ⟨le_max_left _ _, ?_⟩
    calc 2 ^ (BN + max 1 BN) ≤ 2 ^ (2 * max 1 BN) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 ^ max 1 BN := by rw [pow_mul]; norm_num
      _ ≤ P ^ max 1 BN := Nat.pow_le_pow_left hP _

/-- The modulus bound of `lem:residue`, paper/paper.tex: for every `p ∈ 𝒫`,
`p^e > 2^{B_N} ≥ 2 · 2^S · 2^{mk} · (N²Q)^{2m}`, written with `2^{mk} = N^8` and `m = 4`. -/
theorem Parameters.modulus_bound (Pm : Parameters) (p : ℕ) (hp : p ∈ Pm.primes) :
    2 * 2 ^ Pm.S * Pm.N ^ 8 * (Pm.Q * Pm.N ^ 2) ^ 8 < p ^ Pm.e := by
  have hm := Pm.m_eq
  have hspec := primeExponent_spec Pm.BN Pm.P (by have := Pm.P_ge; omega)
  rw [← Pm.e_eq] at hspec
  obtain ⟨he1, he⟩ := hspec
  -- `2 · 2^S · N^8 · (QN²)^8 ≤ 2^{B_N}`
  have hN8 : Pm.N ^ 8 = 2 ^ (Pm.m * Pm.k) := by
    rw [Pm.N_eq, ← pow_mul, hm]
    congr 1
    have := Pm.k_even
    omega
  have hclog : Pm.N ^ 2 * Pm.Q ≤ 2 ^ Nat.clog 2 (Pm.N ^ 2 * Pm.Q) := Nat.le_pow_clog (by norm_num) _
  have hB : 2 * 2 ^ Pm.S * Pm.N ^ 8 * (Pm.Q * Pm.N ^ 2) ^ 8 ≤ 2 ^ Pm.BN := by
    rw [Pm.BN_eq, hN8, hm]
    have h8 : (Pm.Q * Pm.N ^ 2) ^ 8 ≤ (2 ^ Nat.clog 2 (Pm.N ^ 2 * Pm.Q)) ^ 8 :=
      Nat.pow_le_pow_left (by rw [mul_comm]; exact hclog) 8
    calc 2 * 2 ^ Pm.S * 2 ^ (4 * Pm.k) * (Pm.Q * Pm.N ^ 2) ^ 8
        ≤ 2 * 2 ^ Pm.S * 2 ^ (4 * Pm.k) * (2 ^ Nat.clog 2 (Pm.N ^ 2 * Pm.Q)) ^ 8 :=
          Nat.mul_le_mul_left _ h8
      _ = 2 ^ (Pm.S + 4 * Pm.k + 2 * 4 * Nat.clog 2 (Pm.N ^ 2 * Pm.Q) + 1) := by
          rw [← pow_mul]; ring
  -- `2^{B_N} < p^e`, from `2^{B_N + e} ≤ P^e < (2p)^e`
  have hP2 : Pm.P < 2 * p := Pm.primes_gt p hp
  have hlt : Pm.P ^ Pm.e < (2 * p) ^ Pm.e := Nat.pow_lt_pow_left hP2 (by omega)
  have hpe : 2 ^ Pm.BN < p ^ Pm.e := by
    have h := he.trans_lt hlt
    rw [pow_add, mul_pow, mul_comm (2 ^ Pm.BN)] at h
    exact Nat.lt_of_mul_lt_mul_left h
  exact hB.trans_lt hpe

/-- `sec:params` item 6: the exponent `e = e_P` is at least `1` (the hypothesis `e ≥ 1` of `lem:residue`). -/
theorem Parameters.e_pos (Pm : Parameters) : 1 ≤ Pm.e := by
  rw [Pm.e_eq]
  exact (primeExponent_spec Pm.BN Pm.P (by have := Pm.P_ge; omega)).1

theorem pairWindow_pos (Dprime : ℕ) : 1 ≤ pairWindow Dprime := by
  unfold pairWindow
  simp only
  split_ifs with h
  · exact le_rfl
  · omega

/-- `L_w ≥ 1`: both `D' = 1 + Σ_{p ∈ 𝒫}(p - 1)` and `L_2` are positive. -/
theorem Parameters.Lw_pos (Pm : Parameters) : 1 ≤ Pm.Lw := by
  rw [Pm.Lw_eq]
  split_ifs
  · rw [Pm.L2_eq]
    exact pairWindow_pos _
  · rw [Pm.Dprime_eq]
    unfold NearCubicGates.ScalarWindow.window
    omega

/-- `sec:params`, paper/paper.tex: the outcome of the parameter rules. -/
def plan (c : CallShape) : Plan :=
  if c.n < 4 then .soundDefault
  else if c.W = 0 then .exactEvaluation
  else match parameters c with
    | some P => .run P
    | none => .soundDefault

/-! ### The witness -/

/-- The witness of `sec:algorithm`, paper/paper.tex: (W1) a partition index in `[2^k]`; (W2) the set
`𝒮`, one bit per occurrence label `(j, i)`; (W3) vectors `ξ^{(j)}_r ∈ {0,1}^{G_j}` for `j ∈ 𝒥` and `1 ≤ r ≤ J`
(indexed here by `r < J`). -/
structure Witness (k J : ℕ) (G : Fin 2 → ℕ) where
  partitionIndex : Fin (2 ^ k)
  selected : (j : Fin 2) → Fin (G j) → Bool
  vectors : (j : Fin 2) → Fin J → Fin (G j) → Bool

/-- The bit at position `i` of a witness word; missing bits are read as zeros (`sec:algorithm`, paper/paper.tex). -/
def witnessBit (bits : List Bool) (i : ℕ) : Bool := bits.getD i false

/-- The witness read from a binary word (`sec:algorithm`, paper/paper.tex), in the order (W1), (W2), (W3): the first
`k` bits give the partition index (lowest bit first), the next `G_1 + G_2` bits give `𝒮`, and the next
`J (G_1 + G_2)` bits give the vectors `ξ`. Missing or malformed bits are read as zeros, so every word is a witness;
the length `k + (J + 1)(G_1 + G_2)` is polynomial. -/
def decodeWitness (k J : ℕ) (G : Fin 2 → ℕ) (bits : List Bool) : Witness k J G where
  partitionIndex := ⟨(∑ i ∈ Finset.range k, if witnessBit bits i then 2 ^ i else 0) % 2 ^ k,
    Nat.mod_lt _ (by positivity)⟩
  selected := fun j i => witnessBit bits (k + (if j = 0 then 0 else G 0) + i)
  vectors := fun j r i => witnessBit bits
    (k + (G 0 + G 1) + r * (G 0 + G 1) + (if j = 0 then 0 else G 0) + i)

end NearQuarticWires.Algorithm
