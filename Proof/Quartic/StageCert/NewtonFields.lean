import Proof.Quartic.StageCert.BinomialProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens

/-- `lem:maskpoly`, paper/paper.tex: canonical integer
sign of the exact forward-difference cutoff coefficient. -/
def newtonSign (tau a : ℕ) : ℕ := if a=0 then 0 else if a≤tau then 0 else (a-tau)%2

/-- `lem:maskpoly`, paper/paper.tex: exact binary
magnitude of the cutoff coefficient, including all vanishing indices. -/
def newtonMagnitude (tau a : ℕ) : ℕ := if a=0 then 1 else if a≤tau then 0 else (a-1).choose tau

/-- `lem:maskpoly`, paper/paper.tex: the binary sign
and magnitude fields use the literal original integer codec, including zero. -/
theorem newtonFields_exact (tau a : ℕ) :
    newtonSign tau a=(if Mask.newtonCoeff tau a<0 then 1 else 0) ∧
      newtonMagnitude tau a=(Mask.newtonCoeff tau a).natAbs := by
  by_cases ha : a=0
  · simp [newtonSign,newtonMagnitude,StageLift.newtonCoeff_closed,ha]
  · by_cases hle : a≤tau
    · simp [newtonSign,newtonMagnitude,StageLift.newtonCoeff_closed,ha,hle]
    · have hp : 0<(a-1).choose tau := Nat.choose_pos (by omega)
      rw [StageLift.newtonCoeff_closed,if_neg ha,if_neg hle,neg_one_pow_eq_pow_mod_two]
      rcases Nat.mod_two_eq_zero_or_one (a-tau) with he | he
      · simp [newtonSign,newtonMagnitude,ha,hle,he]
      · have hz : (a-1).choose tau≠0 := by omega
        simp [newtonSign,newtonMagnitude,ha,hle,he,hz]

end NearQuarticWires.StageCert.Tokens
