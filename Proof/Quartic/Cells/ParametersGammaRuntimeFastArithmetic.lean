import Proof.Quartic.Cells.ParametersGammaRuntimeCompiler

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `prop:time`, paper/paper.tex: a once-only cache
and a linear-census compiled computation share one seed polynomial. -/
theorem gamma_pipe_scalar_bound (cache compiled A B E s : ℕ)
    (hs : 1 ≤ s) (hE : 1 ≤ E)
    (hcache : cache ≤ A * (E * s ^ 4))
    (hcompiled : compiled ≤ B * (E * s ^ 24)) :
    4 * cache + 4 * compiled + 12 ≤ (4 * A + 4 * B + 12) * (E * s ^ 24) := by
  have hcache24 := hcache.trans (Nat.mul_le_mul_left A
    (Nat.mul_le_mul_left E (Nat.pow_le_pow_right hs (by norm_num : 4 ≤ 24))))
  have h1 : 1 ≤ E * s ^ 24 := by
    simpa only [one_mul] using Nat.mul_le_mul hE (Nat.one_le_pow 24 s hs)
  have h12 := Nat.mul_le_mul_left 12 h1
  calc
    4 * cache + 4 * compiled + 12 ≤
        4 * (A * (E * s ^ 24)) + 4 * (B * (E * s ^ 24)) + 12 * (E * s ^ 24) := by omega
    _ = _ := by ring

/-- `prop:time`, paper/paper.tex: a seed length
linear in the original arity converts any fixed seed polynomial
without changing the independent choice census. -/
theorem gamma_arity_scalar_bound (value C E s a n : ℕ)
    (hvalue : value ≤ C * (E * (s + 9) ^ 24))
    (hs : s ≤ a * (n + 1)) :
    value ≤ (C * (a + 9) ^ 24) * E * (n + 1) ^ 24 := by
  have hshift : s + 9 ≤ (a + 9) * (n + 1) := by nlinarith only [hs]
  calc
    value ≤ C * (E * (s + 9) ^ 24) := hvalue
    _ ≤ C * (E * ((a + 9) * (n + 1)) ^ 24) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshift _))
    _ = _ := by rw [mul_pow]; ring

end NearQuarticWires.Cells.ParameterArithmetic
