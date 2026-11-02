import Proof.Quartic.StageMain.MainSizes
import Proof.Quartic.Cells.ParametersGammaSetup
import Proof.Quartic.Machine.Counts

/-!
# Charging the main census to the three-term time envelope

`prop:time`, paper/paper.tex: the sampled pass
uses the second term. The once-only field search uses the third term,
with its exponential factor retained and bounded by the exact finite
sample-exponent rule of `lem:asymptotics`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicGates.Close.Interfaces

def ledgerExponent (B1 e : ℕ) : ℕ := 8 * (2 * B1 + 100) + e

def ledgerCoefficient (e : ℕ) : ℕ := 2 ^ e + 16 * 2 ^ (8 + e)

theorem selected_census_le {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (e : ℕ) :
    (2 ^ (c.n - p.1.k) * p.1.Q + 2 ^ (2 * p.1.ellf)) * (c.n + 1) ^ e ≤
      ledgerCoefficient e * Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda
        (ledgerExponent B1 e) := by
  have hs := Cells.prepare_spec _ p.1 p.2
  have core : Cells.CoreRules (Builder.callInput c) p.1 := hs
  have hn : 1 ≤ c.n := core.n_pos
  have hnlog : c.n ≤ 2 ^ p.1.lambda := by
    rw [core.lambda_eq]
    exact Nat.le_pow_clog (by decide) _
  have hnext : c.n + 1 ≤ 2 ^ (p.1.lambda + 1) := by
    have hp : 1 ≤ 2 ^ p.1.lambda := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hadm := (Program.dispatch_admitted hd).1
  have hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hq := hs.Qexp_four_upper B1 hb
  have hgamma := Machine.walkGammaPolynomialCost_le c.n p.1.k p.1.Qexp (2 * B1 + 100)
    p.1.lambda e p.1.Q (by rw [hs.Q_eq]) hq hnext
  let E := Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda (ledgerExponent B1 e)
  have hsample : (2 ^ (c.n - p.1.k) * p.1.Q) * (c.n + 1) ^ e ≤ 2 ^ e * E := by
    have hp : (c.n + 1) ^ e ≤ 2 ^ e * c.n ^ e := by
      calc
        _ ≤ (2 * c.n) ^ e := Nat.pow_le_pow_left (by omega) _
        _ = _ := mul_pow _ _ _
    have hex : c.n ^ e ≤ c.n ^ ledgerExponent B1 e := Nat.pow_le_pow_right hn (by unfold ledgerExponent; omega)
    calc
      _ ≤ (2 ^ (c.n - p.1.k) * p.1.Q) * (2 ^ e * c.n ^ ledgerExponent B1 e) :=
        Nat.mul_le_mul_left _ (hp.trans (Nat.mul_le_mul_left _ hex))
      _ = 2 ^ e * (2 ^ (c.n - p.1.k) * p.1.Q * c.n ^ ledgerExponent B1 e) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
  have hfield : 2 ^ (2 * p.1.ellf) * (c.n + 1) ^ e ≤ (16 * 2 ^ (8 + e)) * E := by
    have hsfield := core.field_search_le_gamma_census
    have hwalk : (p.1.Q + 1) ^ 8 * (c.n + 1) ^ e ≤
        2 ^ (4 * p.1.k) * (p.1.Q + 1) ^ 8 * (c.n + 1) ^ e := by
      have hh := Nat.le_mul_of_pos_left ((p.1.Q + 1) ^ 8) (Nat.two_pow_pos (4 * p.1.k))
      exact Nat.mul_le_mul_right _ hh
    calc
      _ ≤ 16 * ((p.1.Q + 1) ^ 8 * (c.n + 1) ^ e) := by
        have hh := Nat.mul_le_mul_right ((c.n + 1) ^ e) hsfield
        simpa only [Nat.mul_assoc] using hh
      _ ≤ 16 * 2 ^ (10 * p.1.k + (8 * (2 * B1 + 100) + e) * p.1.lambda + 8 + e) :=
        Nat.mul_le_mul_left _ (hwalk.trans hgamma)
      _ = (16 * 2 ^ (8 + e)) * 2 ^ (10 * p.1.k + ledgerExponent B1 e * p.1.lambda) := by
        unfold ledgerExponent
        rw [show 10 * p.1.k + (8 * (2 * B1 + 100) + e) * p.1.lambda + 8 + e =
          (8 + e) + (10 * p.1.k + (8 * (2 * B1 + 100) + e) * p.1.lambda) by omega, pow_add]
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  unfold ledgerCoefficient
  change _ ≤ (2 ^ e + 16 * 2 ^ (8 + e)) * E
  nlinarith only [hsample, hfield]

end NearQuarticWires.StageMain.Runtime
