import Proof.Gates.CertifiedScoreSupport

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators

/-- Paper `lem:moments`, paper/paper.tex: the literal signed integer even
moment over the actual finite point/walk index set. -/
def momentSum {V : Type*} [Fintype V] (K : ℕ) (v : V → ℤ) : ℤ :=
  ∑ x, v x ^ (2 * K)

/-- Paper `lem:moments`, paper/paper.tex: a strict moment test bounds EVERY
value on the complete finite index set; no honest-sampling premise occurs. -/
theorem moment_sound {V : Type*} [Fintype V] (K R : ℕ) (v : V → ℤ)
    (htest : momentSum K v < (R : ℤ) ^ (2 * K)) :
    ∀ x, (v x).natAbs < R :=
  NearCubicGates.CertifiedScoreSupport.finite_integer_moment_sound K R v htest

/-- Paper `lem:moments`, paper/paper.tex: the converse for ANY finite index
set of cardinality at most `2^K`, with the precise `sqrt 2` slack. -/
theorem moment_complete {V : Type*} [Fintype V] (K : ℕ) (hK : 1 ≤ K)
    (v : V → ℤ) (R : ℕ) (R' : ℝ) (hcard : Fintype.card V ≤ 2 ^ K)
    (hR' : 0 ≤ R') (hbound : ∀ x, (v x).natAbs ≤ R')
    (hmargin : Real.sqrt 2 * R' < (R : ℝ)) :
    momentSum K v < (R : ℤ) ^ (2 * K) :=
  NearCubicGates.CountingCore.finite_integer_moment_complete K hK v R R'
    hcard hR' hbound hmargin

/-- Paper `eq:testE`/`eq:testPhi`, paper/paper.tex: a masked moment is the
literal test consulted AFTER exactness of the integer mask is certified. -/
def maskedMoment {V : Type*} [Fintype V] (K : ℕ) (mask v : V → ℤ) : ℤ :=
  ∑ x, mask x * v x ^ (2 * K)

/-- Paper `lem:certify`(b), paper/paper.tex: nonnegative exact Boolean masks
allow the strict moment test to bound every retained walk, with signed digits. -/
theorem masked_moment_sound {V : Type*} [Fintype V] (K R : ℕ)
    (mask v : V → ℤ) (hmask : ∀ x, mask x = 0 ∨ mask x = 1)
    (htest : maskedMoment K mask v < (R : ℤ) ^ (2 * K))
    (x : V) (hx : mask x = 1) : (v x).natAbs < R := by
  classical
  have hnonneg (y : V) : 0 ≤ mask y * v y ^ (2 * K) := by
    rcases hmask y with hy | hy <;> rw [hy]
    · simp
    · simpa using even_two_mul K |>.pow_nonneg (v y)
  have hsingle := Finset.single_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) =>
    hnonneg y) (Finset.mem_univ x)
  rw [hx, one_mul] at hsingle
  have hpower : v x ^ (2 * K) < (R : ℤ) ^ (2 * K) := hsingle.trans_lt htest
  rw [NearCubicGates.CountingCore.even_power_eq_magnitude] at hpower
  have hp : (v x).natAbs ^ (2 * K) < R ^ (2 * K) := by exact_mod_cast hpower
  by_contra hn
  have := Nat.pow_le_pow_left (by omega : R ≤ (v x).natAbs) (2 * K)
  omega

end NearQuarticWires.Walks
