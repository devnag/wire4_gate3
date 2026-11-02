import Proof.Quartic.StageCert.MomentFramedPrice

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires

/-- `lem:print` and `prop:time`, paper/paper.tex: all terms of one whole test retain the identical
original call, proposed witness and five-field test metadata. -/
def MomentRequest.withIndex {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (index : Fin (momentTermCount r.selected.1.N r.test)) : MomentRequest B1 B2 :=
  {r with index:=index}

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: population has N² terms and
digit/final moments have N⁸ terms, both within the exact 2^(4k) census. -/
theorem MomentRequest.term_count_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    momentTermCount r.selected.1.N r.test≤2^(4*r.selected.1.k) := by
  have hN : 1≤r.selected.1.N := (Cells.ParameterRules.N_ge_two r.rules).trans' (by decide)
  have hcount : momentTermCount r.selected.1.N r.test≤r.selected.1.N^8 := by
    cases r.test with
    | population => exact Nat.pow_le_pow_right hN (by decide : 2≤8)
    | digit _ _ _ => exact le_rfl
    | finalError _ _ => exact le_rfl
  apply hcount.trans
  rw [r.rules.N_eq,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- `prop:time`, paper/paper.tex: summing the
actual framed source clocks over precisely the whole test's terms
costs a fixed original-arity polynomial per outer column. -/
theorem MomentRequest.framedSourceBudget_sum_terms {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (∑ i : Fin (momentTermCount r.selected.1.N r.test), (r.withIndex i).framedSourceBudget)≤
      framedPriceCoefficient B1 B2*(r.call.n+1)^framedPriceExponent B1 B2*
        2^(r.call.n-r.selected.1.k) := by
  classical
  let A := framedPriceCoefficient B1 B2*(r.call.n+1)^framedPriceExponent B1 B2
  let P := (((Builder.allGates r.call).length+1)^r.selected.1.Xmax)^4
  have hsum : (∑ i : Fin (momentTermCount r.selected.1.N r.test),
      (r.withIndex i).framedSourceBudget)≤
        momentTermCount r.selected.1.N r.test*(A*P) := by
    calc
      _≤∑ _i : Fin (momentTermCount r.selected.1.N r.test), A*P :=
        Finset.sum_le_sum (fun i _=>(r.withIndex i).framedSourceBudget_arity)
      _=_ := by simp
  calc
    _ ≤ momentTermCount r.selected.1.N r.test*(A*P) := hsum
    _≤2^(4*r.selected.1.k)*(A*P) := Nat.mul_le_mul_right _ r.term_count_le
    _=A*(2^(4*r.selected.1.k)*P) := by ring
    _≤A*2^(r.call.n-r.selected.1.k) := Nat.mul_le_mul_left _ r.formatted_tuple_reserve

end NearQuarticWires.StageCert.Tokens
