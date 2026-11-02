import Proof.Quartic.Program.Assembly

/-!
# Cost ledgers of Step 3

Paper: `prop:time`, paper/paper.tex. Step 3 makes `2S` child evaluations and
`S = O(k + λ)`; a polynomial number of repetitions of a step whose cost has the shape of the ledger
`poly(call word) + K · (2^{n-k} n^{2J_max+e} + 2^{n-k} Q n^e + 2^{10k+eλ})` again has this shape, because
`n ≤ 2^λ` with `λ = ⌈lg n⌉`, so a factor `n^a` is absorbed by raising the exponent `e` to `e + a`.

* `propTimeEnvelope_mul_pow`: `n^a · E_e ≤ E_{e+a}` for the three-term envelope `E_e` when `n ≤ 2^λ`.
* `runEnvelope_mul_pow`: the same on the envelope of every call, with the factor `(n+1)^a ≤ 2^a n^a`.
* `LedgerCost.add`, `LedgerCost.of_poly`, `LedgerCost.mul_poly`: sums of ledger costs, polynomial costs, and
  polynomial multiples of ledger costs are ledger costs.
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- `prop:time`, paper/paper.tex: a factor `n^a` is absorbed by the three-term envelope at the
exponent `e + a`, when `n ≤ 2^λ`. -/
theorem propTimeEnvelope_mul_pow (n k Q J lam e a : ℕ) (hn : n ≤ 2 ^ lam) :
    n ^ a * Machine.propTimeEnvelope n k Q J lam e ≤ Machine.propTimeEnvelope n k Q J lam (e + a) := by
  unfold Machine.propTimeEnvelope
  have h3 : n ^ a * 2 ^ (10 * k + e * lam) ≤ 2 ^ (10 * k + (e + a) * lam) := by
    calc n ^ a * 2 ^ (10 * k + e * lam) ≤ (2 ^ lam) ^ a * 2 ^ (10 * k + e * lam) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn a)
      _ = 2 ^ (10 * k + (e + a) * lam) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
  have h1 : n ^ a * (2 ^ (n - k) * n ^ (2 * J + e)) = 2 ^ (n - k) * n ^ (2 * J + (e + a)) := by ring
  have h2 : n ^ a * (2 ^ (n - k) * Q * n ^ e) = 2 ^ (n - k) * Q * n ^ (e + a) := by ring
  rw [mul_add, mul_add, h1, h2]
  omega

/-- The envelope of a call absorbs a factor `(n+1)^a`: on a dispatched call `4 ≤ n ≤ 2^λ` with `λ = ⌈lg n⌉`
(`sec:params`), and off dispatch the envelope is `0`. -/
theorem runEnvelope_mul_pow (e a : ℕ) (c : Call) :
    (c.n + 1) ^ a * runEnvelope B1 B2 e c ≤ 2 ^ a * runEnvelope B1 B2 (e + a) c := by
  unfold runEnvelope
  split
  · rename_i p hp
    have hn : 4 ≤ c.n := (dispatch_admitted hp).1.1
    have hlam : c.n ≤ 2 ^ p.1.lambda := by
      rw [(Cells.prepare_spec _ p.1 p.2).lambda_eq]
      exact Nat.le_pow_clog (by norm_num) _
    calc (c.n + 1) ^ a * Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda e
        ≤ (2 * c.n) ^ a * Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda e :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) a)
      _ = 2 ^ a * (c.n ^ a * Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda e) := by
          rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ a * Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda (e + a) :=
          Nat.mul_le_mul_left _ (propTimeEnvelope_mul_pow _ _ _ _ _ _ _ hlam)
  · simp

/-- On every call, a power of the call word length times the envelope is a constant times the envelope at a larger
exponent (the call word of a normalized call has polynomial length in `n`, `Program.callWord_pow_le`). -/
theorem callWord_pow_mul_runEnvelope (a e : ℕ) : ∃ C d : ℕ, ∀ c : Call,
    ((callWord c).length + 1) ^ a * runEnvelope B1 B2 e c ≤ C * runEnvelope B1 B2 (e + d) c := by
  obtain ⟨C, d, hC⟩ := callWord_pow_le (B1 := B1) (B2 := B2) a
  refine ⟨C * 2 ^ d, d, fun c => ?_⟩
  cases hd : dispatch B1 B2 c with
  | none =>
    have h0 : runEnvelope B1 B2 e c = 0 := by unfold runEnvelope; rw [hd]
    rw [h0, Nat.mul_zero]
    exact Nat.zero_le _
  | some p =>
    have hadm := (dispatch_admitted hd).1
    calc ((callWord c).length + 1) ^ a * runEnvelope B1 B2 e c
        ≤ C * (c.n + 1) ^ d * runEnvelope B1 B2 e c := Nat.mul_le_mul_right _ (hC c hadm)
      _ = C * ((c.n + 1) ^ d * runEnvelope B1 B2 e c) := by rw [mul_assoc]
      _ ≤ C * (2 ^ d * runEnvelope B1 B2 (e + d) c) := Nat.mul_le_mul_left _ (runEnvelope_mul_pow e d c)
      _ = C * 2 ^ d * runEnvelope B1 B2 (e + d) c := by rw [mul_assoc]

/-- A polynomial cost is a ledger cost. -/
theorem LedgerCost.of_poly {f : Call → List Bool → ℕ} (hf : PolyCost f) : LedgerCost B1 B2 f := by
  obtain ⟨K, e, h⟩ := hf
  exact ⟨K, e, fun c w => (h c w).trans (Nat.le_add_right _ _)⟩

/-- The sum of two ledger costs is a ledger cost. -/
theorem LedgerCost.add {f g : Call → List Bool → ℕ} (hf : LedgerCost B1 B2 f) (hg : LedgerCost B1 B2 g) :
    LedgerCost B1 B2 (fun c w => f c w + g c w) := by
  obtain ⟨Kf, ef, hf⟩ := hf
  obtain ⟨Kg, eg, hg⟩ := hg
  refine ⟨2 * (Kf + Kg), ef + eg, fun c w => ?_⟩
  have h1 := LedgerCost.raise (B1 := B1) (B2 := B2) (show Kf ≤ Kf + Kg by omega) (show ef ≤ ef + eg by omega) hf c w
  have h2 := LedgerCost.raise (B1 := B1) (B2 := B2) (show Kg ≤ Kf + Kg by omega) (show eg ≤ ef + eg by omega) hg c w
  dsimp only
  nlinarith

/-- **A polynomial multiple of a ledger cost is a ledger cost** (`prop:time`: the `2S` child
evaluations of Step 3, with `S` polynomial). -/
theorem LedgerCost.mul_poly {f g : Call → List Bool → ℕ} (hf : PolyCost f) (hg : LedgerCost B1 B2 g) :
    LedgerCost B1 B2 (fun c w => f c w * g c w) := by
  obtain ⟨Kf, ef, hf⟩ := hf
  obtain ⟨Kg, eg, hg⟩ := hg
  obtain ⟨C, d, hC⟩ := callWord_pow_mul_runEnvelope (B1 := B1) (B2 := B2) ef eg
  refine ⟨Kf * Kg * (C + 1), ef + eg + d, fun c w => ?_⟩
  set X := (callWord c).length + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hmono := runEnvelope_mono (B1 := B1) (B2 := B2) (show eg + d ≤ ef + eg + d by omega) c
  have hpow : X ^ ef * X ^ eg ≤ X ^ (ef + eg + d) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right hX1 (by omega)
  calc f c w * g c w ≤ (Kf * X ^ ef) * (Kg * X ^ eg + Kg * runEnvelope B1 B2 eg c) :=
        Nat.mul_le_mul (hf c w) (hg c w)
    _ = Kf * Kg * (X ^ ef * X ^ eg) + Kf * Kg * (X ^ ef * runEnvelope B1 B2 eg c) := by ring
    _ ≤ Kf * Kg * X ^ (ef + eg + d) + Kf * Kg * (C * runEnvelope B1 B2 (ef + eg + d) c) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ hpow
        · exact Nat.mul_le_mul_left _ ((hC c).trans (Nat.mul_le_mul_left _ hmono))
    _ ≤ Kf * Kg * (C + 1) * X ^ (ef + eg + d) + Kf * Kg * (C + 1) * runEnvelope B1 B2 (ef + eg + d) c := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
        · rw [mul_assoc (Kf * Kg) (C + 1)]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

/-- On a dispatched call, a power of `n + 1` is below the envelope: `(n+1)^D ≤ 2^D · E_D`, since the third term of
the envelope at the exponent `0` is at least `1`. -/
theorem pow_le_runEnvelope (D : ℕ) {c : Call} {p : Selected c} (h : dispatch B1 B2 c = some p) :
    (c.n + 1) ^ D ≤ 2 ^ D * runEnvelope B1 B2 D c := by
  have h1 := runEnvelope_mul_pow (B1 := B1) (B2 := B2) 0 D c
  rw [zero_add] at h1
  have h0 : 1 ≤ runEnvelope B1 B2 0 c := by
    unfold runEnvelope
    rw [h]
    dsimp only
    unfold Machine.propTimeEnvelope
    have : 1 ≤ 2 ^ (10 * p.1.k + 0 * p.1.lambda) := Nat.one_le_two_pow
    omega
  calc (c.n + 1) ^ D = (c.n + 1) ^ D * 1 := (mul_one _).symm
    _ ≤ (c.n + 1) ^ D * runEnvelope B1 B2 0 c := Nat.mul_le_mul_left _ h0
    _ ≤ 2 ^ D * runEnvelope B1 B2 D c := h1

/-- **A factor polynomial in `n` on dispatched calls, times a ledger cost, is a ledger cost** (`prop:time`: Step 3 repeats a child evaluation `2S` times with `S = O(k + λ)`). Off dispatch the factor is bounded by
a constant. -/
theorem LedgerCost.mul_dispatched {f g : Call → List Bool → ℕ} (K d : ℕ)
    (hf0 : ∀ c w, dispatch B1 B2 c = none → f c w ≤ K)
    (hf1 : ∀ c w (p : Selected c), dispatch B1 B2 c = some p → f c w ≤ K * (c.n + 1) ^ d)
    (hg : LedgerCost B1 B2 g) : LedgerCost B1 B2 (fun c w => f c w * g c w) := by
  obtain ⟨Kg, eg, hg⟩ := hg
  obtain ⟨C, d', hC⟩ := callWord_pow_le (B1 := B1) (B2 := B2) eg
  set E := eg + d + d' with hE
  set A := K * Kg * (C + 1) * 2 ^ (d + d') with hA
  refine ⟨A, E, fun c w => ?_⟩
  set X := (callWord c).length + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hXE : X ^ eg ≤ X ^ E := Nat.pow_le_pow_right hX1 (by omega)
  have hRE : runEnvelope B1 B2 eg c ≤ runEnvelope B1 B2 E c := runEnvelope_mono (by omega) c
  have hA1 : K * Kg ≤ A := by
    have h2 : 1 ≤ (C + 1) * 2 ^ (d + d') := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc K * Kg = K * Kg * 1 := (mul_one _).symm
      _ ≤ K * Kg * ((C + 1) * 2 ^ (d + d')) := Nat.mul_le_mul_left _ h2
      _ = A := by rw [hA]; ring
  have hgcw := hg c w
  cases hd : dispatch B1 B2 c with
  | none =>
    have hf := hf0 c w hd
    calc f c w * g c w ≤ K * (Kg * X ^ eg + Kg * runEnvelope B1 B2 eg c) := Nat.mul_le_mul hf hgcw
      _ = K * Kg * X ^ eg + K * Kg * runEnvelope B1 B2 eg c := by ring
      _ ≤ A * X ^ E + A * runEnvelope B1 B2 E c := Nat.add_le_add (Nat.mul_le_mul hA1 hXE) (Nat.mul_le_mul hA1 hRE)
  | some p =>
    have hf := hf1 c w p hd
    have hadm := (dispatch_admitted hd).1
    -- the polynomial part is absorbed by the envelope
    have hpoly : (c.n + 1) ^ d * X ^ eg ≤ C * 2 ^ (d + d') * runEnvelope B1 B2 E c := by
      calc (c.n + 1) ^ d * X ^ eg ≤ (c.n + 1) ^ d * (C * (c.n + 1) ^ d') := Nat.mul_le_mul_left _ (hC c hadm)
        _ = C * (c.n + 1) ^ (d + d') := by rw [pow_add]; ring
        _ ≤ C * (2 ^ (d + d') * runEnvelope B1 B2 (d + d') c) := Nat.mul_le_mul_left _ (pow_le_runEnvelope _ hd)
        _ ≤ C * (2 ^ (d + d') * runEnvelope B1 B2 E c) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (runEnvelope_mono (by omega) c))
        _ = C * 2 ^ (d + d') * runEnvelope B1 B2 E c := by ring
    have henv : (c.n + 1) ^ d * runEnvelope B1 B2 eg c ≤ 2 ^ (d + d') * runEnvelope B1 B2 E c := by
      calc (c.n + 1) ^ d * runEnvelope B1 B2 eg c ≤ 2 ^ d * runEnvelope B1 B2 (eg + d) c := runEnvelope_mul_pow _ _ c
        _ ≤ 2 ^ (d + d') * runEnvelope B1 B2 E c :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (runEnvelope_mono (by omega) c)
    calc f c w * g c w ≤ K * (c.n + 1) ^ d * (Kg * X ^ eg + Kg * runEnvelope B1 B2 eg c) := Nat.mul_le_mul hf hgcw
      _ = K * Kg * ((c.n + 1) ^ d * X ^ eg) + K * Kg * ((c.n + 1) ^ d * runEnvelope B1 B2 eg c) := by ring
      _ ≤ K * Kg * (C * 2 ^ (d + d') * runEnvelope B1 B2 E c) +
          K * Kg * (2 ^ (d + d') * runEnvelope B1 B2 E c) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hpoly) (Nat.mul_le_mul_left _ henv)
      _ = A * runEnvelope B1 B2 E c := by rw [hA]; ring
      _ ≤ A * X ^ E + A * runEnvelope B1 B2 E c := Nat.le_add_left _ _

end NearQuarticWires.Greedy
