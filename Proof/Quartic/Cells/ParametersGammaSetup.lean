import Proof.Quartic.Cells.ParametersGuards
import Proof.Quartic.Greedy.Child

set_option autoImplicit false

namespace NearQuarticWires.Cells

namespace CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- The finite-field degree is at most twice the binary sample
exponent plus two, `imp:seed` and `prop:time`, paper/paper.tex. -/
theorem ellf_le_twice_sample_exponent (hs : CoreRules x p) : p.ellf ≤ 2 * p.Qexp + 2 := by
  have hNQ := hs.N_le_Q
  rw [hs.N_eq, hs.Q_eq] at hNQ
  have hk : p.k / 2 ≤ p.Qexp := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hNQ
  rw [hs.ellf_eq]
  omega

/-- The once-only field search is paid by four powers of the
actual sample count, `prop:time`, paper/paper.tex. -/
theorem field_search_le_sample_four (hs : CoreRules x p) :
    2 ^ (2 * p.ellf) ≤ 16 * p.Q ^ 4 := by
  calc
    2 ^ (2 * p.ellf) ≤ 2 ^ (4 * p.Qexp + 4) :=
      Nat.pow_le_pow_right (by norm_num) (by have := hs.ellf_le_twice_sample_exponent; omega)
    _ = 2 ^ 4 * (2 ^ p.Qexp) ^ 4 := by
      rw [show 4 * p.Qexp + 4 = 4 + p.Qexp * 4 by omega, pow_add, pow_mul]
    _ = 16 * p.Q ^ 4 := by rw [hs.Q_eq]; norm_num

/-- The actual coefficient budget also pays the once-only field
setup, `prop:time`, paper/paper.tex. -/
theorem field_search_le_gamma_census (hs : CoreRules x p) :
    2 ^ (2 * p.ellf) ≤ 16 * (p.Q + 1) ^ 8 := by
  apply hs.field_search_le_sample_four.trans
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) (by norm_num))

end CoreRules

/-- The exact requests used by the greedy coefficient control
satisfy the field-search charge, uniformly over every walk and
prefix, `prop:time`, paper/paper.tex. -/
theorem gammaRequest_field_search_bound {B1 B2 : ℕ} (q : Greedy.ChildRequest B1 B2)
    (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    2 ^ (2 * (Greedy.gammaRequest q w).parameters.ell) ≤ 16 * (q.selected.1.Q + 1) ^ 8 := by
  have hs := prepare_spec _ q.selected.1 q.selected.2
  exact CoreRules.field_search_le_gamma_census (hs : CoreRules (Builder.callInput q.call) q.selected.1)

end NearQuarticWires.Cells
