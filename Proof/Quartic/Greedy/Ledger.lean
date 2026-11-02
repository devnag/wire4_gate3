import Proof.Quartic.Greedy.Child

/-!
# The cost of one child evaluation

Paper: `prop:time`, paper/paper.tex.

"Step 3 has `2S` child evaluations. Each computes `|W_s| ≤ 2^{mk}` coefficients in `(Q+1)^{2m} poly(n)` time each,
prints at most `4^m |𝒫| P^{2J+2} ≤ 4^m P^{2J+3}` tables, and solves at most `n_c 4^m (2h_E)^{2J} ≤ 2^{n-k} 4^m P^{2J}`
exact systems", each of polynomial size. With `N^{2m} = 2^{mk} = 2^{4k}`, `Q ≤ 2^{3k/4 + (2B₁+100)λ}`
(`Cells.ParameterRules.Qexp_upper`), `P ≤ n` and `J ≤ J_max`, the coefficients cost `2^{10k + O(λ)}`, the tables and
the systems cost `2^{n-k} n^{2J_max + O(1)}`, and the copies of the word after Step 2 cost its length: every term is
a term of the three-term envelope, or the length of `certWord` times a polynomial.

* `envelope_columns`, `envelope_inner`: the first and third terms of the envelope.
* `childArith`: the arithmetic of the bound, over the natural numbers.
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program

/-! ## The terms of the envelope -/

/-- The first term of the envelope of `prop:time`: `2^{n-k} n^{2J_max + a} ≤ E_a`. -/
theorem envelope_columns (n k Q Jmax lam a : ℕ) :
    2 ^ (n - k) * n ^ (2 * Jmax + a) ≤ Machine.propTimeEnvelope n k Q Jmax lam a := by
  unfold Machine.propTimeEnvelope
  exact le_add_right (le_add_right le_rfl)

/-- The third term of the envelope of `prop:time`: `2^{10k + bλ} n^a ≤ E_{b+a}` when `n ≤ 2^λ`. -/
theorem envelope_inner (n k Q Jmax lam a b : ℕ) (hn : n ≤ 2 ^ lam) :
    2 ^ (10 * k + b * lam) * n ^ a ≤ Machine.propTimeEnvelope n k Q Jmax lam (b + a) := by
  unfold Machine.propTimeEnvelope
  have h : 2 ^ (10 * k + b * lam) * n ^ a ≤ 2 ^ (10 * k + (b + a) * lam) :=
    calc 2 ^ (10 * k + b * lam) * n ^ a ≤ 2 ^ (10 * k + b * lam) * (2 ^ lam) ^ a :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn a)
      _ = 2 ^ (10 * k + (b + a) * lam) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
  exact h.trans (Nat.le_add_left _ _)

/-- `(n+1)^a ≤ 2^a n^a` for `n ≥ 1`. -/
theorem succ_pow_le (n a : ℕ) (hn : 1 ≤ n) : (n + 1) ^ a ≤ 2 ^ a * n ^ a := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by omega) a

/-- The envelope is monotone in its exponent for `n ≥ 1`. -/
theorem envelope_mono (n k Q Jmax lam : ℕ) (hn : 1 ≤ n) {a b : ℕ} (h : a ≤ b) :
    Machine.propTimeEnvelope n k Q Jmax lam a ≤ Machine.propTimeEnvelope n k Q Jmax lam b :=
  Cells.ParameterArithmetic.time_envelope_mono _ _ _ _ _ _ _ (by omega) h

/-- A factor `(n+1)^a` is absorbed by the envelope at the exponent `e + a`. -/
theorem envelope_succ_mul (n k Q Jmax lam e a : ℕ) (hn1 : 1 ≤ n) (hlam : n ≤ 2 ^ lam) :
    (n + 1) ^ a * Machine.propTimeEnvelope n k Q Jmax lam e ≤
      2 ^ a * Machine.propTimeEnvelope n k Q Jmax lam (e + a) := by
  calc (n + 1) ^ a * Machine.propTimeEnvelope n k Q Jmax lam e
      ≤ (2 ^ a * n ^ a) * Machine.propTimeEnvelope n k Q Jmax lam e :=
        Nat.mul_le_mul_right _ (succ_pow_le n a hn1)
    _ = 2 ^ a * (n ^ a * Machine.propTimeEnvelope n k Q Jmax lam e) := by ring
    _ ≤ 2 ^ a * Machine.propTimeEnvelope n k Q Jmax lam (e + a) :=
        Nat.mul_le_mul_left _ (propTimeEnvelope_mul_pow _ _ _ _ _ _ _ hlam)

/-- The coefficient stage (`prop:time`): `N^{2m} (Q+1)^{2m}` with `N^{2m} ≤ 2^{4k}` and
`(Q+1)^{2m} ≤ 2^8 · 2^{6k + bλ}` is a third term of the envelope. -/
theorem coefficients_le (n k N Q Jmax lam b Kγ eγ : ℕ) (hn1 : 1 ≤ n) (hlam : n ≤ 2 ^ lam)
    (hN : N ^ 8 ≤ 2 ^ (4 * k)) (hQ : (Q + 1) ^ 8 ≤ 2 ^ 8 * 2 ^ (6 * k + b * lam)) :
    (N ^ 8 + 1) * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ) ≤
      Kγ * 2 ^ (9 + eγ) * Machine.propTimeEnvelope n k Q Jmax lam (b + eγ) := by
  have hN1 : N ^ 8 + 1 ≤ 2 * 2 ^ (4 * k) := by
    have : 1 ≤ 2 ^ (4 * k) := Nat.one_le_two_pow
    omega
  calc (N ^ 8 + 1) * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ)
      = Kγ * ((N ^ 8 + 1) * (Q + 1) ^ 8) * (n + 1) ^ eγ := by ring
    _ ≤ Kγ * ((2 * 2 ^ (4 * k)) * (2 ^ 8 * 2 ^ (6 * k + b * lam))) * (2 ^ eγ * n ^ eγ) := by
        gcongr
        exact succ_pow_le n eγ hn1
    _ = Kγ * 2 ^ (9 + eγ) * (2 ^ (10 * k + b * lam) * n ^ eγ) := by ring
    _ ≤ Kγ * 2 ^ (9 + eγ) * Machine.propTimeEnvelope n k Q Jmax lam (b + eγ) :=
        Nat.mul_le_mul_left _ (envelope_inner _ _ _ _ _ _ _ hlam)

/-- The overhead of the coefficient stage per walk: `N^{2m} ((n+1)^e + S)` with `S ≤ s₀(n+1)`. -/
theorem walkOverhead_le (n k N Q Jmax lam S s0 e1 : ℕ) (hn1 : 1 ≤ n) (hlam : n ≤ 2 ^ lam)
    (hN : N ^ 8 ≤ 2 ^ (4 * k)) (hS : S ≤ s0 * (n + 1)) :
    (N ^ 8 + 1) * ((n + 1) ^ e1 + S) ≤
      2 * (1 + s0) * 2 ^ (e1 + 1) * Machine.propTimeEnvelope n k Q Jmax lam (0 + (e1 + 1)) := by
  have hN1 : N ^ 8 + 1 ≤ 2 * 2 ^ (10 * k + 0 * lam) := by
    have h1 : 1 ≤ 2 ^ (4 * k) := Nat.one_le_two_pow
    have h2 : 2 ^ (4 * k) ≤ 2 ^ (10 * k + 0 * lam) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp1 : (n + 1) ^ e1 ≤ (n + 1) ^ (e1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : n + 1 ≤ (n + 1) ^ (e1 + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (e1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hinner : (n + 1) ^ e1 + S ≤ (1 + s0) * (2 ^ (e1 + 1) * n ^ (e1 + 1)) := by
    have h3 := succ_pow_le n (e1 + 1) hn1
    have h4 : (n + 1) ^ e1 + S ≤ (1 + s0) * (n + 1) ^ (e1 + 1) := by nlinarith
    exact h4.trans (Nat.mul_le_mul_left _ h3)
  calc (N ^ 8 + 1) * ((n + 1) ^ e1 + S)
      ≤ (2 * 2 ^ (10 * k + 0 * lam)) * ((1 + s0) * (2 ^ (e1 + 1) * n ^ (e1 + 1))) := Nat.mul_le_mul hN1 hinner
    _ = 2 * (1 + s0) * 2 ^ (e1 + 1) * (2 ^ (10 * k + 0 * lam) * n ^ (e1 + 1)) := by ring
    _ ≤ 2 * (1 + s0) * 2 ^ (e1 + 1) * Machine.propTimeEnvelope n k Q Jmax lam (0 + (e1 + 1)) :=
        Nat.mul_le_mul_left _ (envelope_inner _ _ _ _ _ _ _ hlam)

/-- The exact systems (`prop:time`): `2 · 2^{n-k} 4^m P^{2(J+1)}` systems, each with at most `P^3`
rows and one solve of polynomial cost, form a first term of the envelope. -/
theorem systemsSolve_le (n k Q P J Jmax lam Ks es e0 : ℕ) (hn1 : 1 ≤ n) (hP : P ≤ n)
    (hJ : J - 1 + 1 ≤ Jmax + 1) :
    2 * 2 ^ (n - k) * 4 ^ 4 * P ^ (2 * (J - 1 + 1)) * (P ^ 3 + Ks * ((n + 1) ^ e0 + 1) ^ es + 1) ≤
      512 * (1 + (Ks + 1) * 2 ^ ((e0 + 1) * es)) * Machine.propTimeEnvelope n k Q Jmax lam (5 + e0 * es) := by
  have hY : (n + 1) ^ e0 + 1 ≤ 2 ^ (e0 + 1) * n ^ e0 := by
    have h1 := succ_pow_le n e0 hn1
    have h2 : 1 ≤ 2 ^ e0 * n ^ e0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [pow_succ]
    nlinarith
  have hsol : Ks * ((n + 1) ^ e0 + 1) ^ es + 1 ≤ (Ks + 1) * 2 ^ ((e0 + 1) * es) * n ^ (e0 * es) := by
    have h1 : 1 ≤ ((n + 1) ^ e0 + 1) ^ es := Nat.one_le_pow _ _ (by omega)
    have h2 : ((n + 1) ^ e0 + 1) ^ es ≤ 2 ^ ((e0 + 1) * es) * n ^ (e0 * es) := by
      calc ((n + 1) ^ e0 + 1) ^ es ≤ (2 ^ (e0 + 1) * n ^ e0) ^ es := Nat.pow_le_pow_left hY _
        _ = 2 ^ ((e0 + 1) * es) * n ^ (e0 * es) := by rw [mul_pow, ← pow_mul, ← pow_mul]
    calc Ks * ((n + 1) ^ e0 + 1) ^ es + 1 ≤ (Ks + 1) * ((n + 1) ^ e0 + 1) ^ es := by nlinarith
      _ ≤ (Ks + 1) * (2 ^ ((e0 + 1) * es) * n ^ (e0 * es)) := Nat.mul_le_mul_left _ h2
      _ = (Ks + 1) * 2 ^ ((e0 + 1) * es) * n ^ (e0 * es) := by ring
  have hinner : P ^ 3 + Ks * ((n + 1) ^ e0 + 1) ^ es + 1 ≤
      (1 + (Ks + 1) * 2 ^ ((e0 + 1) * es)) * n ^ (3 + e0 * es) := by
    have hP3 : P ^ 3 ≤ n ^ (3 + e0 * es) :=
      (Nat.pow_le_pow_left hP 3).trans (Nat.pow_le_pow_right hn1 (by omega))
    have hb : n ^ (e0 * es) ≤ n ^ (3 + e0 * es) := Nat.pow_le_pow_right hn1 (by omega)
    calc P ^ 3 + Ks * ((n + 1) ^ e0 + 1) ^ es + 1
        = P ^ 3 + (Ks * ((n + 1) ^ e0 + 1) ^ es + 1) := by ring
      _ ≤ n ^ (3 + e0 * es) + (Ks + 1) * 2 ^ ((e0 + 1) * es) * n ^ (3 + e0 * es) :=
          Nat.add_le_add hP3 (hsol.trans (Nat.mul_le_mul_left _ hb))
      _ = (1 + (Ks + 1) * 2 ^ ((e0 + 1) * es)) * n ^ (3 + e0 * es) := by ring
  have hPJ : P ^ (2 * (J - 1 + 1)) ≤ n ^ (2 * Jmax + 2) :=
    (Nat.pow_le_pow_left hP _).trans (Nat.pow_le_pow_right hn1 (by omega))
  calc 2 * 2 ^ (n - k) * 4 ^ 4 * P ^ (2 * (J - 1 + 1)) * (P ^ 3 + Ks * ((n + 1) ^ e0 + 1) ^ es + 1)
      ≤ 2 * 2 ^ (n - k) * 4 ^ 4 * n ^ (2 * Jmax + 2) *
          ((1 + (Ks + 1) * 2 ^ ((e0 + 1) * es)) * n ^ (3 + e0 * es)) := by gcongr
    _ = 512 * (1 + (Ks + 1) * 2 ^ ((e0 + 1) * es)) * (2 ^ (n - k) * n ^ (2 * Jmax + (5 + e0 * es))) := by ring
    _ ≤ 512 * (1 + (Ks + 1) * 2 ^ ((e0 + 1) * es)) * Machine.propTimeEnvelope n k Q Jmax lam (5 + e0 * es) :=
        Nat.mul_le_mul_left _ (envelope_columns _ _ _ _ _ _)

/-- The printed tables with the copies of their inputs (`prop:time`): each of the
`2 · 4^m P^{2(J+1)+3}` tables costs one printing `K_p 2^{n-k}(n+1)^{e_p}`, the copy of the word after parameter
preparation (`L_p ≤ K_q (n+1)^{e_q}`), the copy of the coefficient table (`L_g`, at most `2^{4k}` entries of
`(Q+1)^{2m} poly(n)` bits), its `2^{n-k}` records and its indices; with `10k ≤ n - k` (`sec:params`, the initial
degree test) and `2^λ ≤ 2n` this is a first term of the envelope. -/
theorem tablesCopy_le (n k N Q P J Jmax lam b Kγ eγ Kp ep Kq eq e0 Lp Lg : ℕ) (hn1 : 1 ≤ n) (hk : k ≤ n)
    (hk10 : 10 * k ≤ n - k) (hlam2 : 2 ^ lam ≤ 2 * n) (hN : N ^ 8 ≤ 2 ^ (4 * k))
    (hQ : (Q + 1) ^ 8 ≤ 2 ^ 8 * 2 ^ (6 * k + b * lam)) (hP : P ≤ n) (hJ : J - 1 + 1 ≤ Jmax + 1)
    (hLp : Lp ≤ Kq * (n + 1) ^ eq)
    (hLg : Lg ≤ 2 * (8 * k + 3 + N ^ 8 * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + 1)) + 1) :
    2 * 4 ^ 4 * P ^ (2 * (J - 1 + 1) + 3) *
        (Kp * (2 ^ (n - k) * (n + 1) ^ ep + ((n + 1) ^ e0 + 1) ^ ep) + Lp + Lg + 2 ^ (n - k) + (n + 1) ^ e0) ≤
      512 * (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * 2 ^ (ep + eq + e0 + b + eγ + 1 + e0 * ep) *
        Machine.propTimeEnvelope n k Q Jmax lam (5 + (ep + eq + e0 + b + eγ + 1 + e0 * ep)) := by
  set a := ep + eq + e0 + b + eγ + 1 + e0 * ep with ha
  set U := 2 ^ (n - k) * (n + 1) ^ a with hU
  have hpow : ∀ x, x ≤ a → (n + 1) ^ x ≤ (n + 1) ^ a := fun x hx => Nat.pow_le_pow_right (by omega) hx
  have h2 : 1 ≤ 2 ^ (n - k) := Nat.one_le_two_pow
  have hU1 : ∀ x, x ≤ a → (n + 1) ^ x ≤ U := fun x hx =>
    (hpow x hx).trans (by rw [hU]; exact Nat.le_mul_of_pos_left _ (by positivity))
  have hp1 : Kp * (2 ^ (n - k) * (n + 1) ^ ep + ((n + 1) ^ e0 + 1) ^ ep) ≤ Kp * (1 + 2 ^ ep) * U := by
    have hY : (n + 1) ^ e0 + 1 ≤ 2 * (n + 1) ^ e0 := by
      have : 1 ≤ (n + 1) ^ e0 := Nat.one_le_pow _ _ (by omega)
      omega
    have hY2 : ((n + 1) ^ e0 + 1) ^ ep ≤ 2 ^ ep * U := by
      calc ((n + 1) ^ e0 + 1) ^ ep ≤ (2 * (n + 1) ^ e0) ^ ep := Nat.pow_le_pow_left hY _
        _ = 2 ^ ep * (n + 1) ^ (e0 * ep) := by rw [mul_pow, ← pow_mul]
        _ ≤ 2 ^ ep * U := Nat.mul_le_mul_left _ (hU1 _ (by rw [ha]; omega))
    have hX : 2 ^ (n - k) * (n + 1) ^ ep ≤ U := by
      rw [hU]
      exact Nat.mul_le_mul_left _ (hpow ep (by omega))
    calc Kp * (2 ^ (n - k) * (n + 1) ^ ep + ((n + 1) ^ e0 + 1) ^ ep) ≤ Kp * (U + 2 ^ ep * U) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add hX hY2)
      _ = Kp * (1 + 2 ^ ep) * U := by ring
  have hp2 : Lp ≤ Kq * U := hLp.trans (Nat.mul_le_mul_left _ (hU1 eq (by omega)))
  have hp3 : 2 ^ (n - k) ≤ U := by
    rw [hU]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hp4 : (n + 1) ^ e0 ≤ U := hU1 e0 (by omega)
  -- the coefficient table
  have hp5 : Lg ≤ (23 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * U := by
    have hlin : 16 * k + 7 ≤ 23 * U := by
      have := hU1 1 (by omega)
      rw [pow_one] at this
      omega
    have hb : 2 ^ (b * lam) ≤ 2 ^ b * (n + 1) ^ b := by
      calc 2 ^ (b * lam) = (2 ^ lam) ^ b := by rw [← pow_mul, mul_comm]
        _ ≤ (2 * n) ^ b := Nat.pow_le_pow_left hlam2 b
        _ = 2 ^ b * n ^ b := mul_pow _ _ _
        _ ≤ 2 ^ b * (n + 1) ^ b := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) b)
    have h10 : 2 ^ (10 * k) ≤ 2 ^ (n - k) := Nat.pow_le_pow_right (by norm_num) hk10
    have hg1 : Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + 1 ≤ (Kγ + 1) * ((Q + 1) ^ 8 * (n + 1) ^ eγ) := by
      have : 1 ≤ (Q + 1) ^ 8 * (n + 1) ^ eγ := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have hNg : N ^ 8 * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + 1) ≤ (Kγ + 1) * 2 ^ (8 + b) * U := by
      calc N ^ 8 * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + 1)
          ≤ 2 ^ (4 * k) * ((Kγ + 1) * ((2 ^ 8 * 2 ^ (6 * k + b * lam)) * (n + 1) ^ eγ)) := by
            gcongr
            exact hg1.trans (by gcongr)
        _ = (Kγ + 1) * 2 ^ 8 * (2 ^ (10 * k) * 2 ^ (b * lam) * (n + 1) ^ eγ) := by ring
        _ ≤ (Kγ + 1) * 2 ^ 8 * (2 ^ (n - k) * (2 ^ b * (n + 1) ^ b) * (n + 1) ^ eγ) := by gcongr
        _ = (Kγ + 1) * 2 ^ (8 + b) * (2 ^ (n - k) * (n + 1) ^ (b + eγ)) := by ring
        _ ≤ (Kγ + 1) * 2 ^ (8 + b) * U := by
            apply Nat.mul_le_mul_left
            rw [hU]
            exact Nat.mul_le_mul_left _ (hpow _ (by omega))
    calc Lg ≤ 2 * (8 * k + 3 + N ^ 8 * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + 1)) + 1 := hLg
      _ = (16 * k + 7) + 2 * (N ^ 8 * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + 1)) := by ring
      _ ≤ 23 * U + 2 * ((Kγ + 1) * 2 ^ (8 + b) * U) := Nat.add_le_add hlin (Nat.mul_le_mul_left _ hNg)
      _ = (23 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * U := by ring
  have hinner : Kp * (2 ^ (n - k) * (n + 1) ^ ep + ((n + 1) ^ e0 + 1) ^ ep) + Lp + Lg + 2 ^ (n - k) + (n + 1) ^ e0 ≤
      (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * U := by
    have := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp1 hp2) hp5) hp3) hp4
    calc _ ≤ Kp * (1 + 2 ^ ep) * U + Kq * U + (23 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * U + U + U := this
      _ = (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * U := by ring
  have hPn : P ^ (2 * (J - 1 + 1) + 3) ≤ n ^ (2 * Jmax + 5) :=
    (Nat.pow_le_pow_left hP _).trans (Nat.pow_le_pow_right hn1 (by omega))
  calc 2 * 4 ^ 4 * P ^ (2 * (J - 1 + 1) + 3) *
        (Kp * (2 ^ (n - k) * (n + 1) ^ ep + ((n + 1) ^ e0 + 1) ^ ep) + Lp + Lg + 2 ^ (n - k) + (n + 1) ^ e0)
      ≤ 2 * 4 ^ 4 * n ^ (2 * Jmax + 5) * ((Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) *
          (2 ^ (n - k) * (2 ^ a * n ^ a))) := by
        gcongr
        rw [hU] at hinner
        exact hinner.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (succ_pow_le n a hn1)))
    _ = 512 * (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * 2 ^ a *
        (2 ^ (n - k) * n ^ (2 * Jmax + (5 + a))) := by
        ring
    _ ≤ 512 * (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) * 2 ^ a *
        Machine.propTimeEnvelope n k Q Jmax lam (5 + a) :=
        Nat.mul_le_mul_left _ (envelope_columns _ _ _ _ _ _)

/-- **The arithmetic of the cost of one child evaluation** (`prop:time`): the two stage bounds are
at most `A (n+1)^d (L+1) + A E_{E}` for constants `A`, `d`, `E` depending only on the constants of the controls
and of the subroutines; here `L` is the length of the word after Step 2. -/
theorem childArith (K1 e1 Kγ eγ Kp ep Ks es e0 K2 e2 b s0 Kq eq : ℕ) : ∃ A d E : ℕ,
    ∀ n k N Q S P J Jmax lam L Lp Lg : ℕ, 1 ≤ n → n ≤ 2 ^ lam → N ^ 8 ≤ 2 ^ (4 * k) →
      (Q + 1) ^ 8 ≤ 2 ^ 8 * 2 ^ (6 * k + b * lam) → P ≤ n → J - 1 + 1 ≤ Jmax + 1 → S ≤ s0 * (n + 1) →
      k ≤ n → 10 * k ≤ n - k → 2 ^ lam ≤ 2 * n → Lp ≤ Kq * (n + 1) ^ eq →
      Lg ≤ 2 * (8 * k + 3 + N ^ 8 * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + 1)) + 1 →
      K1 * ((N ^ 8 + 1) * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + (n + 1) ^ e1 + S) + (L + 2 * S + 1) + 1) +
        K2 * (n + 1) ^ e2 *
          (2 * 4 ^ 4 * P ^ (2 * (J - 1 + 1) + 3) *
              (Kp * (2 ^ (n - k) * (n + 1) ^ ep + ((n + 1) ^ e0 + 1) ^ ep) + Lp + Lg + 2 ^ (n - k) +
                (n + 1) ^ e0) +
            2 * 2 ^ (n - k) * 4 ^ 4 * P ^ (2 * (J - 1 + 1)) *
              (P ^ 3 + Ks * ((n + 1) ^ e0 + 1) ^ es + 1) +
            K1 * ((N ^ 8 + 1) * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + (n + 1) ^ e1 + S) + (L + 2 * S + 1) + 1) + 1) ≤
        A * (n + 1) ^ d * (L + 1) + A * Machine.propTimeEnvelope n k Q Jmax lam E := by
  set M := 1 + (Ks + 1) * 2 ^ ((e0 + 1) * es) with hM
  set C1 := K1 * (Kγ * 2 ^ (9 + eγ) + 2 * (1 + s0) * 2 ^ (e1 + 1)) with hC1
  set C2 := K1 * (2 * s0 + 2) with hC2
  set D1 := 512 * (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) *
    2 ^ (ep + eq + e0 + b + eγ + 1 + e0 * ep) * 2 ^ e2 with hD1
  set D2 := 512 * M * 2 ^ e2 with hD2
  set E := b + eγ + e1 + 1 + e2 + 5 + ep + eq + e0 + e0 * es + 1 + e0 * ep with hE
  refine ⟨(C1 + K2 * (D1 + D2 + C1 * 2 ^ e2)) + (C2 + K2 * (C2 + 1)), e2 + 1, E,
    fun n k N Q S P J Jmax lam L Lp Lg hn1 hlam hN hQ hP hJ hS hk hk10 hlam2 hLp hLg => ?_⟩
  have hL : L + 2 * S + 1 + 1 ≤ (2 * s0 + 2) * ((n + 1) * (L + 1)) := by
    have h1 : s0 * (n + 1) ≤ s0 * ((n + 1) * (L + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    have h2 : L + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : (2 * s0 + 2) * ((n + 1) * (L + 1)) = 2 * (s0 * ((n + 1) * (L + 1))) + 2 * ((n + 1) * (L + 1)) := by
      ring
    rw [h3]
    omega
  set R := fun x => Machine.propTimeEnvelope n k Q Jmax lam x with hR
  have hmono : ∀ x, x ≤ E → R x ≤ R E := fun x hx => envelope_mono n k Q Jmax lam hn1 hx
  have hsm : ∀ x, x + e2 ≤ E → (n + 1) ^ e2 * R x ≤ 2 ^ e2 * R E := fun x hx =>
    (envelope_succ_mul n k Q Jmax lam x e2 hn1 hlam).trans (Nat.mul_le_mul_left _ (hmono _ hx))
  have hγ := coefficients_le n k N Q Jmax lam b Kγ eγ hn1 hlam hN hQ
  have ho := walkOverhead_le n k N Q Jmax lam S s0 e1 hn1 hlam hN hS
  have t1 := tablesCopy_le n k N Q P J Jmax lam b Kγ eγ Kp ep Kq eq e0 Lp Lg hn1 hk hk10 hlam2 hN hQ hP hJ hLp hLg
  have t2 := systemsSolve_le n k Q P J Jmax lam Ks es e0 hn1 hP hJ
  set Z := (n + 1) ^ (e2 + 1) * (L + 1) with hZ
  set GsF := K1 * ((N ^ 8 + 1) * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ + (n + 1) ^ e1 + S) + (L + 2 * S + 1) + 1)
    with hGsF
  set T1 := 2 * 4 ^ 4 * P ^ (2 * (J - 1 + 1) + 3) *
    (Kp * (2 ^ (n - k) * (n + 1) ^ ep + ((n + 1) ^ e0 + 1) ^ ep) + Lp + Lg + 2 ^ (n - k) + (n + 1) ^ e0) with hT1
  set T2 := 2 * 2 ^ (n - k) * 4 ^ 4 * P ^ (2 * (J - 1 + 1)) *
    (P ^ 3 + Ks * ((n + 1) ^ e0 + 1) ^ es + 1) with hT2
  -- the pieces
  have hZ1 : (n + 1) * (L + 1) ≤ Z := by
    rw [hZ]
    apply Nat.mul_le_mul_right
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (e2 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hGsplit : GsF = K1 * ((N ^ 8 + 1) * (Kγ * (Q + 1) ^ 8 * (n + 1) ^ eγ)) +
      K1 * ((N ^ 8 + 1) * ((n + 1) ^ e1 + S)) + K1 * (L + 2 * S + 1 + 1) := by
    rw [hGsF]; ring
  -- the coefficient stage
  have hG : GsF ≤ K1 * (Kγ * 2 ^ (9 + eγ) * R (b + eγ)) + K1 * (2 * (1 + s0) * 2 ^ (e1 + 1) * R (0 + (e1 + 1))) +
      C2 * ((n + 1) * (L + 1)) := by
    rw [hGsplit, hC2, mul_assoc K1]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hγ) (Nat.mul_le_mul_left _ ho))
      (Nat.mul_le_mul_left _ hL)
  have hG1 : GsF ≤ C1 * R E + C2 * Z := by
    have r1 := hmono (b + eγ) (by omega)
    have r2 := hmono (0 + (e1 + 1)) (by omega)
    calc GsF ≤ K1 * (Kγ * 2 ^ (9 + eγ) * R (b + eγ)) + K1 * (2 * (1 + s0) * 2 ^ (e1 + 1) * R (0 + (e1 + 1))) +
          C2 * ((n + 1) * (L + 1)) := hG
      _ ≤ K1 * (Kγ * 2 ^ (9 + eγ) * R E) + K1 * (2 * (1 + s0) * 2 ^ (e1 + 1) * R E) + C2 * Z := by gcongr
      _ = C1 * R E + C2 * Z := by rw [hC1]; ring
  have hG2 : (n + 1) ^ e2 * GsF ≤ C1 * 2 ^ e2 * R E + C2 * Z := by
    have r1 := hsm (b + eγ) (by omega)
    have r2 := hsm (0 + (e1 + 1)) (by omega)
    have hZe : (n + 1) ^ e2 * ((n + 1) * (L + 1)) = Z := by rw [hZ]; ring
    calc (n + 1) ^ e2 * GsF ≤ (n + 1) ^ e2 * (K1 * (Kγ * 2 ^ (9 + eγ) * R (b + eγ)) +
          K1 * (2 * (1 + s0) * 2 ^ (e1 + 1) * R (0 + (e1 + 1))) + C2 * ((n + 1) * (L + 1))) :=
          Nat.mul_le_mul_left _ hG
      _ = K1 * Kγ * 2 ^ (9 + eγ) * ((n + 1) ^ e2 * R (b + eγ)) +
          K1 * (2 * (1 + s0) * 2 ^ (e1 + 1)) * ((n + 1) ^ e2 * R (0 + (e1 + 1))) +
          C2 * ((n + 1) ^ e2 * ((n + 1) * (L + 1))) := by ring
      _ ≤ K1 * Kγ * 2 ^ (9 + eγ) * (2 ^ e2 * R E) + K1 * (2 * (1 + s0) * 2 ^ (e1 + 1)) * (2 ^ e2 * R E) +
          C2 * Z := by rw [hZe]; gcongr
      _ = C1 * 2 ^ e2 * R E + C2 * Z := by rw [hC1]; ring
  -- the reconstruction stage
  have h3 : (n + 1) ^ e2 * T1 ≤ D1 * R E := by
    have t := t1
    have r := hsm (5 + (ep + eq + e0 + b + eγ + 1 + e0 * ep)) (by omega)
    calc (n + 1) ^ e2 * T1 ≤ (n + 1) ^ e2 * (512 * (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) *
          2 ^ (ep + eq + e0 + b + eγ + 1 + e0 * ep) * R (5 + (ep + eq + e0 + b + eγ + 1 + e0 * ep))) :=
          Nat.mul_le_mul_left _ t
      _ = 512 * (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) *
          2 ^ (ep + eq + e0 + b + eγ + 1 + e0 * ep) *
          ((n + 1) ^ e2 * R (5 + (ep + eq + e0 + b + eγ + 1 + e0 * ep))) := by ring
      _ ≤ 512 * (Kp * (1 + 2 ^ ep) + Kq + 25 + 2 * (Kγ + 1) * 2 ^ (8 + b)) *
          2 ^ (ep + eq + e0 + b + eγ + 1 + e0 * ep) * (2 ^ e2 * R E) := Nat.mul_le_mul_left _ r
      _ = D1 * R E := by rw [hD1]; ring
  have h4 : (n + 1) ^ e2 * T2 ≤ D2 * R E := by
    have t := t2
    have r := hsm (5 + e0 * es) (by omega)
    calc (n + 1) ^ e2 * T2 ≤ (n + 1) ^ e2 * (512 * M * R (5 + e0 * es)) := Nat.mul_le_mul_left _ t
      _ = 512 * M * ((n + 1) ^ e2 * R (5 + e0 * es)) := by ring
      _ ≤ 512 * M * (2 ^ e2 * R E) := Nat.mul_le_mul_left _ r
      _ = D2 * R E := by rw [hD2]; ring
  have h5 : (n + 1) ^ e2 ≤ Z := by
    rw [hZ]
    calc (n + 1) ^ e2 ≤ (n + 1) ^ (e2 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = (n + 1) ^ (e2 + 1) * 1 := (mul_one _).symm
      _ ≤ (n + 1) ^ (e2 + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have hRs : K2 * (n + 1) ^ e2 * (T1 + T2 + GsF + 1) ≤
      K2 * (D1 + D2 + C1 * 2 ^ e2) * R E + K2 * (C2 + 1) * Z := by
    calc K2 * (n + 1) ^ e2 * (T1 + T2 + GsF + 1) =
        K2 * ((n + 1) ^ e2 * T1 + (n + 1) ^ e2 * T2 + (n + 1) ^ e2 * GsF + (n + 1) ^ e2) := by ring
      _ ≤ K2 * (D1 * R E + D2 * R E + (C1 * 2 ^ e2 * R E + C2 * Z) + Z) := by gcongr
      _ = K2 * (D1 + D2 + C1 * 2 ^ e2) * R E + K2 * (C2 + 1) * Z := by ring
  show GsF + K2 * (n + 1) ^ e2 * (T1 + T2 + GsF + 1) ≤ _
  calc GsF + K2 * (n + 1) ^ e2 * (T1 + T2 + GsF + 1)
      ≤ (C1 * R E + C2 * Z) + (K2 * (D1 + D2 + C1 * 2 ^ e2) * R E + K2 * (C2 + 1) * Z) :=
        Nat.add_le_add hG1 hRs
    _ = (C1 + K2 * (D1 + D2 + C1 * 2 ^ e2)) * R E + (C2 + K2 * (C2 + 1)) * Z := by ring
    _ ≤ ((C1 + K2 * (D1 + D2 + C1 * 2 ^ e2)) + (C2 + K2 * (C2 + 1))) * R E +
        ((C1 + K2 * (D1 + D2 + C1 * 2 ^ e2)) + (C2 + K2 * (C2 + 1))) * Z :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
    _ = ((C1 + K2 * (D1 + D2 + C1 * 2 ^ e2)) + (C2 + K2 * (C2 + 1))) * (n + 1) ^ (e2 + 1) * (L + 1) +
        ((C1 + K2 * (D1 + D2 + C1 * 2 ^ e2)) + (C2 + K2 * (C2 + 1))) * R E := by rw [hZ]; ring

end NearQuarticWires.Greedy
