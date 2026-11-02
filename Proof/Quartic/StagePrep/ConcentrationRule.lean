import Proof.Gates.Counter.Eventual
import Proof.Quartic.Cells.ParametersArithmetic

/-!
# The concentration search and the canonical positive logarithm

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Counter
open Cells.ParameterArithmetic

/-- The exact exponent substitution in `sec:params`,
paper/paper.tex, for the integer concentration test. -/
def concentrationExponent (m k : ℕ) : ℕ := m * k + 2 * m + 3

/-- The concentration inequality of `sec:params`,
paper/paper.tex, equals the bounded-search test
after the explicit exponent substitution. -/
theorem concentration_factor (m k J : ℕ) :
    4 * J * 2 ^ concentrationExponent m k = 2 ^ (m * k + 2 * m + 5) * J := by
  rw [show m * k + 2 * m + 5 = concentrationExponent m k + 2 by
    unfold concentrationExponent; omega, pow_add]
  norm_num
  ring

/-- The finite integer search computes exactly the canonical
positive concentration parameter of `sec:params`,
paper/paper.tex. -/
theorem leastT_eq_concentrationT (m k J : ℕ) (beta : ℚ)
    (hbeta : 0 < beta) (hupper : beta ≤ 1 / 16) (hJ : 1 ≤ J) :
    leastT (concentrationExponent m k) J beta = some (concentrationT m k J beta) := by
  obtain ⟨T, hT⟩ := leastT_exists (concentrationExponent m k) J beta hbeta
  obtain ⟨hpass, _, hminimal⟩ := leastUpTo_spec _ _ _ hT
  have hpositive := leastT_pos _ _ _ _ hJ hupper hT
  have hcanonical : concentrationT m k J beta ≤ T := by
    apply (concentrationT_le_iff m k J hbeta T).2
    refine ⟨hpositive, ?_⟩
    simpa only [TPass, concentration_factor] using hpass
  have hcanonicalPass : TPass (concentrationExponent m k) J beta (concentrationT m k J beta) := by
    have hp := ((concentrationT_le_iff m k J hbeta _).1 le_rfl).2
    simpa only [TPass, concentration_factor] using hp
  have hleast : T ≤ concentrationT m k J beta := by
    by_contra hn
    exact hminimal _ (by omega) hcanonicalPass
  have heq : T = concentrationT m k J beta := Nat.le_antisymm hleast hcanonical
  simpa only [heq] using hT

end NearQuarticWires.StagePrep
