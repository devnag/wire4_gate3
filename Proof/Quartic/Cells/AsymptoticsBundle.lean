import Proof.Quartic.Cells.AsymptoticsWindowSize
import Proof.Quartic.Cells.AsymptoticsShape
import Proof.Quartic.Cells.ParametersFast

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic
open NearCubicGates.Close.Interfaces

/-- All displayed scales and precision side conditions of
`lem:asymptotics`, paper/paper.tex, in explicit uniform
integer and raised-power form for the actual selected parameters. -/
structure AsymptoticBounds (B1 : ℕ) (x : ParameterInput) (p : Parameters) : Prop where
  r_exact : p.r = 16 * p.mu
  inner : 8 * p.mu * p.lambda ≤ p.k ∧ p.k ≤ 16 * p.mu * p.lambda
  concentration : 32 * p.mu * p.lambda ≤ p.T ∧ p.T ≤ (B1 + 80) * p.mu * p.lambda
  precision : 8 * p.mu * p.lambda ≤ p.tau ∧ p.tau ≤ (B1 + 20) * p.mu * p.lambda
  population_cap :
    9216 * p.lambda ^ 2 * p.mu ^ 3 * x.n ≤ p.Xmax ^ 2 ∧
      p.Xmax ^ 2 ≤ 600 * (B1 + 20) ^ 2 * p.lambda ^ 2 * p.mu ^ 3 * x.n
  sample_exponent : 4 * p.Qexp ≤ 3 * p.k + 4 * (2 * B1 + 100) * p.lambda
  seed_field_degree : p.ellf = p.k
  seed_length : p.S = 8 * p.k
  numerator : 160 * p.mu * p.lambda ≤ p.BN ∧ p.BN ≤ (32 * B1 + 2200) * p.mu * p.lambda
  degree : x.n ≤ 20000 * p.lambda * p.Dmax ∧ 100 * p.lambda * p.Dmax ≤ x.n
  lift : 160 * p.mu ≤ p.e ∧ p.e ≤ 8 * (32 * B1 + 2200) * p.mu
  prime : 16000 * p.lambda * p.mu ^ 2 * p.P ≤ x.n ∧
    x.n ≤ primeScaleCoefficient B1 * p.lambda * p.mu ^ 2 * p.P
  height : 32 * p.h ≤ p.P ∧ p.P ≤ 64 * p.h
  scalar_lower : p.P ^ 2 ≤ 32 * (p.Dprime - 1) * p.lambda
  scalar_upper : (p.Dprime : ℝ) * p.lambda * Real.log 2 ≤ 16 * (p.P : ℝ) ^ 2
  pair_positive : 2 ≤ p.L2
  pair_lower : p.P ^ 6 ≤ (32 ^ 3 * (16 ^ 3 * 48 ^ 4)) * p.lambda ^ 3 * p.L2 ^ 4
  pair_upper : (p.L2 : ℝ) ^ 4 * (p.lambda : ℝ) ^ 3 * (Real.log 2) ^ 3 ≤ 32768 * (p.P : ℝ) ^ 6
  k_precision : (16 : ℚ) / x.beta ≤ 2 ^ p.k
  population_precision : (2 : ℚ) ^ (2 * p.k) * (64 / x.beta) ^ 2 ≤ 2 ^ p.Xmax

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- The matching lower printing-degree scale in `lem:asymptotics`,
paper/paper.tex, with the floor in the explicit trial
absorbed by a factor of two. -/
theorem degree_lower_scaled (hs : ParameterRules x p)
    (hlarge : 30000 * p.lambda ^ 2 ≤ x.n) : x.n ≤ 20000 * p.lambda * p.Dmax := by
  have hl : 0 < p.lambda := by have := hs.logarithms_pos.1; omega
  have hden : 0 < 10000 * p.lambda := by positivity
  have htrial := (CoreRules.greatest_degree_bounds (hs : CoreRules x p) hlarge).1
  rw [← hs.Dmax_eq] at htrial
  have hLsquare : p.lambda ≤ p.lambda ^ 2 := by nlinarith only [hl]
  have hdiv : 1 ≤ x.n / (10000 * p.lambda) := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    nlinarith only [hlarge, hLsquare]
  have hdpos : 1 ≤ p.Dmax := hdiv.trans htrial
  have hrem := Nat.mod_lt x.n hden
  have hdivision := Nat.mod_add_div x.n (10000 * p.lambda)
  have hmul := Nat.mul_le_mul_left (10000 * p.lambda) htrial
  have hn : x.n ≤ (10000 * p.lambda) * (p.Dmax + 1) := by
    nlinarith only [hrem, hdivision, hmul]
  calc
    x.n ≤ (10000 * p.lambda) * (p.Dmax + 1) := hn
    _ ≤ (10000 * p.lambda) * (2 * p.Dmax) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end ParameterRules

/-- The full `lem:asymptotics`, paper/paper.tex:
one onset uniformly supplies actual canonical parameter selection, every
finite parameter requirement, every displayed scale, and both literal
precision side conditions for all normalized public inputs. -/
theorem eventual_asymptotics
    (B1 : ℕ) :
    ∃ onset : ℕ, 4 ≤ onset ∧ ∀ x : ParameterInput, onset ≤ x.n → ValidInput x →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      ∃ p, prepare x = some p ∧ ParameterRules x p ∧ AsymptoticBounds B1 x p := by
  obtain ⟨os, hos, hs⟩ := eventual_prepare_precision B1
  obtain ⟨osh, hosh, hshape⟩ := CoreRules.eventual_shape_scales B1
  obtain ⟨ol, hol, hlift⟩ := ParameterRules.eventual_lift_prime_scales B1
  obtain ⟨ow, how, hwindow⟩ := ParameterRules.eventual_window_scales B1
  obtain ⟨oseed, hoseed, hseed⟩ := CoreRules.eventual_seed_length B1
  obtain ⟨od, hod, hdegree⟩ := NearCubicGates.Close.Closure.lambda_poly_lt 30000 2
  refine ⟨max os (max osh (max ol (max ow (max oseed od)))), by omega, ?_⟩
  intro x hn hv hb
  obtain ⟨p, hp, hr, hkprec, hXprec⟩ := hs x (by omega) hv hb
  obtain ⟨hk, hT, hτ, hX, hBN⟩ := hshape x p (by omega) (hr : CoreRules x p) hb
  obtain ⟨he, hP⟩ := hlift x p (by omega) hr hb
  obtain ⟨hDlo, hDup, hLlo, hLup⟩ := hwindow x p (by omega) hr hb
  have hseeds := hseed x p (by omega) (hr : CoreRules x p) hb
  have hlarge : 30000 * p.lambda ^ 2 ≤ x.n := by
    rw [hr.lambda_eq]
    exact (hdegree x.n (by omega)).le
  refine ⟨p, hp, hr, {
    r_exact := hr.r_eq
    inner := hk
    concentration := hT
    precision := hτ
    population_cap := hX
    sample_exponent := hr.Qexp_four_upper B1 hb
    seed_field_degree := hseeds.1
    seed_length := hseeds.2
    numerator := hBN
    degree := ⟨hr.degree_lower_scaled hlarge, hr.degree_upper_scaled⟩
    lift := he
    prime := hP
    height := hr.height_scale
    scalar_lower := hDlo
    scalar_upper := hDup
    pair_positive := hLlo.1
    pair_lower := hLlo.2
    pair_upper := hLup
    k_precision := hkprec
    population_precision := hXprec }⟩

/-- `lem:asymptotics` on the actual normalized call representation,
paper/paper.tex, uniformly for all three call
kinds and every positive wire count within the admission envelope. -/
theorem eventual_call_asymptotics
    (B1 B2 : ℕ) :
    ∃ onset : ℕ, 4 ≤ onset ∧ ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c →
      Transfer.callWires c ≠ 0 →
      ∃ p, prepare (Builder.callInput c) = some p ∧ ParameterRules (Builder.callInput c) p ∧
        AsymptoticBounds B1 (Builder.callInput c) p := by
  obtain ⟨onset, hon, h⟩ := eventual_asymptotics B1
  refine ⟨onset, hon, ?_⟩
  intro c hn hadm hW
  exact h (Builder.callInput c) hn (callInput_valid c hadm hW) hadm.2.2.2.2.2.2.2.2.2.1

end NearQuarticWires.Cells
