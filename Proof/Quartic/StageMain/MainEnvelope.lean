import Proof.Quartic.StageMain.FieldExtractSizes
import Proof.Quartic.StageMain.EntryRequest
import Proof.Quartic.Cells.ParametersMainWord

/-!
# A common finite envelope for the main arithmetic

`prop:time`, paper/paper.tex, charges polynomial
work in the original arity around the sampled pass. The envelope
below bounds the actual retained source, field degree, sample exponent,
and the arity-polynomial ordinary entry budget with fixed coefficients.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Bounds

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open Cells.ParameterArithmetic Compact

def coefficient (B1 K : ℕ) : ℕ := capacityCoefficient B1 + preparationCoefficient B1 + K + 1002

def degree (B1 B2 d : ℕ) : ℕ := capacityExponent B1 B2 + (B1 + 12) + d + (B2 + 8) + 2

def envelope (B1 B2 K d n : ℕ) : ℕ := coefficient B1 K * (n + 1) ^ degree B1 B2 d

theorem monomial_le (B1 B2 K d n a e : ℕ) (ha : a ≤ coefficient B1 K)
    (he : e ≤ degree B1 B2 d) : a * (n + 1) ^ e ≤ envelope B1 B2 K d n :=
  Nat.mul_le_mul ha (Nat.pow_le_pow_right (Nat.succ_pos _) he)

theorem envelope_pos (B1 B2 K d n : ℕ) : 1 ≤ envelope B1 B2 K d n := by
  have hp : 1 ≤ (n + 1) ^ degree B1 B2 d := Nat.pow_pos (Nat.succ_pos _)
  unfold envelope coefficient
  nlinarith

theorem arity_le (B1 B2 K d n : ℕ) : n + 1 ≤ envelope B1 B2 K d n := by
  have hh := monomial_le B1 B2 K d n 1 1 (by unfold coefficient; omega) (by unfold degree; omega)
  simpa only [one_mul, pow_one] using hh

theorem preparation_le (B1 B2 K d n : ℕ) :
    preparationEnvelope B1 n ≤ envelope B1 B2 K d n :=
  monomial_le B1 B2 K d n (preparationCoefficient B1) (B1 + 12)
    (by unfold coefficient; omega) (by unfold degree; omega)

theorem entry_budget_le (B1 B2 K d n : ℕ) :
    K * (n + 1) ^ d ≤ envelope B1 B2 K d n :=
  monomial_le B1 B2 K d n K d (by unfold coefficient; omega) (by unfold degree; omega)

theorem compact_le {B1 B2 : ℕ} (K d : ℕ) {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (Program.prepWord B1 B2 c w).length ≤ envelope B1 B2 K d c.n := by
  rw [prepWord_eq_compact hd]
  exact (compactInput_length_arity hd w).trans
    (monomial_le B1 B2 K d c.n _ _ (by unfold coefficient; omega) (by unfold degree; omega))

theorem call_le {B1 B2 : ℕ} (K d : ℕ) {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) :
    (callWord c).length ≤ envelope B1 B2 K d c.n :=
  (CallSize.dispatched_callWord_polynomial hd).trans
    (monomial_le B1 B2 K d c.n _ _ (by unfold coefficient; omega) (by unfold degree; omega))

theorem scalar_le {B1 B2 : ℕ} (K d : ℕ) {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) :
    p.1.ellf ≤ envelope B1 B2 K d c.n ∧ p.1.Qexp ≤ envelope B1 B2 K d c.n := by
  have hadm := (Program.dispatch_admitted hd).1
  have hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hs := (Cells.prepare_spec _ p.1 p.2).scalar_preparation_bounds B1 hb
  exact ⟨hs.ellf.trans (preparation_le B1 B2 K d c.n),
    hs.Qexp.trans (preparation_le B1 B2 K d c.n)⟩

theorem mainWord_le {B1 B2 : ℕ} (K d : ℕ) {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (Program.mainWord B1 B2 c w).length ≤ 400 * envelope B1 B2 K d c.n := by
  have hh := Cells.dispatched_mainWord_envelope hd w
  have he := preparation_le B1 B2 K d c.n
  have hc := call_le K d hd
  have hp := envelope_pos B1 B2 K d c.n
  omega

end NearQuarticWires.StageMain.Bounds
