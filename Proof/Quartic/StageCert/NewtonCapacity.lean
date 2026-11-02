import Proof.Quartic.StageCert.NewtonFields

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: twice the coefficient index, plus two bits, suffices for
all exact binary binomial numerators and natural divisors. -/
theorem binomial_capacity_of_width (n W : ℕ) (hW : 2*n+2≤W) :
    2^n*(n+1)<2^W ∧ 2*(n+1)≤2^W := by
  have hn : n+1≤2^n := Nat.lt_two_pow_self
  have hb : 2^n*(n+1)≤2^(2*n) := by
    calc
      2^n*(n+1)≤2^n*2^n := Nat.mul_le_mul_left _ hn
      _=2^(2*n) := by rw [←pow_add,Nat.two_mul]
  have hp : 2^(2*n+1)≤2^W := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0<2^(2*n) := Nat.two_pow_pos _
  have hs : 2*(n+1)≤2^(n+1) := by
    calc
      2*(n+1)≤2*2^n := Nat.mul_le_mul_left _ hn
      _=2^(n+1) := by rw [pow_succ,Nat.mul_comm]
  refine ⟨?_,hs.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
  rw [pow_succ] at hp
  omega

end NearQuarticWires.StageCert.Tokens
