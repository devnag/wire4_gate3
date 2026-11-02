import Proof.Quartic.Cells.ParametersMomentBits
import Proof.Quartic.Cells.ParametersCallEncoding

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Interfaces
open ParameterArithmetic

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- The total occurrence count fits the same scalar envelope as the
selected parameters, `sec:params` and `prop:time`, paper/paper.tex. -/
theorem occurrences_preparation_envelope (hs : ParameterRules x p) (B1 : ℕ) :
    x.G1 + x.G2 ≤ preparationEnvelope B1 x.n := by
  have hG : x.G1 + x.G2 ≤ 2 * x.n ^ 4 := hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
  calc
    x.G1 + x.G2 ≤ 2 * x.n ^ 4 := hG
    _ ≤ 34 * x.n ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ preparationEnvelope B1 x.n := preparation_envelope_base B1 x.n 34 4
      (by simp [preparationCoefficients]) (by omega)

/-- The exact pre-certification walk-moment range has polynomial
binary height for selected parameters, `eq:testE`–`eq:testPhi` and
`prop:time`, paper/paper.tex. -/
theorem selected_walk_moment_power_bound (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) (rate : ℕ) (hrate : rate ≤ x.n) :
    p.N ^ 8 * ((p.Xmax + 1) * 2 ^ (p.Xmax + (x.G1 + x.G2))) ^ 8 *
      (8 * (x.G1 + x.G2) * (1 + rate + p.M1 + p.A)) ^ (8 * p.k) ≤
        2 ^ certificateBitEnvelope (preparationEnvelope B1 x.n) := by
  have hscalar := hs.scalar_preparation_bounds B1 hb
  have hn : x.n ≤ preparationEnvelope B1 x.n :=
    (Nat.le_succ _).trans (preparation_envelope_arity B1 x.n)
  have hv : preparationEnvelope B1 x.n ≤ 2 ^ preparationEnvelope B1 x.n := Nat.lt_two_pow_self.le
  exact certificate_walk_moment_power_bound _ _ _ _ _ _ _ _ hscalar.k hs.N_eq
    hscalar.Xmax (hs.occurrences_preparation_envelope B1) (hrate.trans (hn.trans hv))
    (hscalar.M1.trans hv) (hscalar.A.trans hv)

/-- Population moments and every literal threshold have the same
pre-certification binary height, `eq:testX`–`eq:testPhi`,
paper/paper.tex. -/
theorem selected_other_moment_power_bounds (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    let V := preparationEnvelope B1 x.n
    p.N ^ 2 * (x.G1 + x.G2) ^ (2 * p.k) ≤ 2 ^ certificateBitEnvelope V ∧
      (p.Xmax + 1) ^ (2 * p.k) ≤ 2 ^ certificateBitEnvelope V ∧
      p.hE ^ (8 * p.k) ≤ 2 ^ certificateBitEnvelope V ∧
      p.Lambda ^ (8 * p.k) ≤ 2 ^ certificateBitEnvelope V := by
  have hscalar := hs.scalar_preparation_bounds B1 hb
  let V := preparationEnvelope B1 x.n
  have hv : V ≤ 2 ^ (V + 1) := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
  have hx : p.Xmax + 1 ≤ 2 ^ (V + 1) :=
    (Nat.add_le_add_right hscalar.Xmax 1).trans Nat.lt_two_pow_self.le
  refine ⟨certificate_population_power_bound _ _ _ _ hscalar.k hs.N_eq
    (hs.occurrences_preparation_envelope B1), ?_, ?_, ?_⟩
  · exact certificate_threshold_power_bound V p.k (p.Xmax + 1) (2 * p.k) hscalar.k hx (by omega)
  · exact certificate_threshold_power_bound V p.k p.hE (8 * p.k) hscalar.k (hscalar.hE.trans hv) le_rfl
  · exact certificate_threshold_power_bound V p.k p.Lambda (8 * p.k) hscalar.k (hscalar.Lambda.trans hv) le_rfl

end ParameterRules

/-- The common binary height is polynomial in the input arity,
`prop:time`, paper/paper.tex. -/
theorem certificate_bit_envelope_polynomial (B1 n : ℕ) :
    certificateBitEnvelope (preparationEnvelope B1 n) ≤
      100 * (preparationCoefficient B1 + 1) ^ 2 * (n + 1) ^ (2 * (B1 + 12)) := by
  have hone : 1 ≤ (n + 1) ^ (B1 + 12) := Nat.pow_pos (Nat.succ_pos _)
  have hbase : preparationEnvelope B1 n + 1 ≤
      (preparationCoefficient B1 + 1) * (n + 1) ^ (B1 + 12) := by
    unfold preparationEnvelope
    nlinarith only [hone]
  have hsquare := Nat.pow_le_pow_left hbase 2
  unfold certificateBitEnvelope
  calc
    100 * (preparationEnvelope B1 n + 1) ^ 2 ≤
        100 * ((preparationCoefficient B1 + 1) * (n + 1) ^ (B1 + 12)) ^ 2 :=
      Nat.mul_le_mul_left _ hsquare
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm (B1 + 12) 2]; ring

/-- The complete pre-certification moment bit height is polynomial
in the actual serialized dispatched call, uniformly in the witness,
`prop:time`, paper/paper.tex. -/
theorem dispatched_certificate_bit_envelope {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) :
    certificateBitEnvelope (preparationEnvelope B1 c.n) ≤
      100 * (preparationCoefficient B1 + 1) ^ 2 *
        ((NearCubicGates.Close.Interfaces.callWord c).length + 1) ^ (2 * (B1 + 12)) := by
  exact (certificate_bit_envelope_polynomial B1 c.n).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (dispatched_n_le_callWord hd) 1) _))

end NearQuarticWires.Cells
