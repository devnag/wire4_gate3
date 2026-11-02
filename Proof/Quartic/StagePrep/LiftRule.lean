import Proof.Quartic.Cells.ParametersArithmetic

/-!
# The finite lifted-prime exponent search

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

/-- The exponent substitution for the exact lift comparison in
`sec:params`, paper/paper.tex. -/
theorem liftPass_encoding (BN P e : ℕ) (hBN : 1 ≤ BN) :
    NearCubicGates.Close.Counter.LiftPass (BN - 1) P e ↔
      Cells.ParameterArithmetic.LiftPass BN P e := by
  unfold NearCubicGates.Close.Counter.LiftPass Cells.ParameterArithmetic.LiftPass
  rw [Nat.sub_add_cancel hBN]

/-- The longer finite search computes the same least exponent
as the canonical search of `sec:params`, paper/paper.tex. Its extra iterations remain part of the program cost. -/
theorem liftExp_eq_liftExponent (BN P : ℕ) (hBN : 1 ≤ BN) (hP : 4 ≤ P) :
    NearCubicGates.Close.Counter.liftExp (BN - 1) P =
      Cells.ParameterArithmetic.liftExponent BN P := by
  obtain ⟨e, he⟩ := Cells.ParameterArithmetic.liftExponent_isSome BN P hP
  obtain ⟨hp, hb, hm⟩ := Cells.ParameterArithmetic.liftExponent_spec BN P e he
  have hbound : e ≤ 2 * (BN - 1 + 1) := by rw [Nat.sub_add_cancel hBN]; omega
  have hold := NearCubicGates.Close.Counter.leastUpTo_eq
    (NearCubicGates.Close.Counter.LiftPass (BN - 1) P) (2 * (BN - 1 + 1)) e hbound
    ((liftPass_encoding BN P e hBN).2 hp)
    (fun t ht hpass => hm t ht ((liftPass_encoding BN P t hBN).1 hpass))
  unfold NearCubicGates.Close.Counter.liftExp
  rw [hold, he]

end NearQuarticWires.StagePrep
