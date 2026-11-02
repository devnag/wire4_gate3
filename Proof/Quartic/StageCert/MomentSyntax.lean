import Proof.Quartic.StageCert.TupleMomentSyntax
import Proof.Quartic.StageCert.MomentRuntimeScale
import Proof.Gates.Expand.Rpn

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires
open NearCubicGates.Close.Tabulator
open Cells.ParameterArithmetic

/-- `lem:print`, paper/paper.tex: complete digit
leaf heights are bounded before any column has been certified. -/
theorem MomentRequest.digit_leaf_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (row : Fin (r.selected.1.J-1+1))
    (g : Fin (Builder.allGates r.call).length) :
    Nat.size (StagePrint.circuitWeights r.call j
      (StagePrint.callDigitWeights r.call r.rules r.retainedWitness j row) g).natAbs≤r.coefficientBits := by
  rw [←source_digit_global_eq_builder]
  exact (NearCubicGates.Close.Expand.size_le_natBitLength _).trans (r.digit_coefficient_bits j row g)

/-- `lem:print`, paper/paper.tex: signed final
offsets have the same unconditional complete-source leaf bound. -/
theorem MomentRequest.final_leaf_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (g : Fin (Builder.allGates r.call).length) :
    Nat.size (StagePrint.circuitWeights r.call j
      (StagePrint.callFinalWeights r.call r.selected.1 r.retainedWitness j) g).natAbs≤r.coefficientBits := by
  rw [←source_final_global_eq_builder]
  exact (NearCubicGates.Close.Expand.size_le_natBitLength _).trans (r.final_coefficient_bits j g)

/-- `lem:print`, paper/paper.tex: the actual
population, digit and final-error source trees satisfy one literal
syntax bound, with guarded tuple construction retained. -/
theorem MomentRequest.formula_size_bound {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.formula.size≤
      8*((r.selected.1.Xmax+1)*(((Builder.allGates r.call).length+1)^r.selected.1.Xmax*
        (11*r.selected.1.Xmax+4)+4)+4)+82*(Builder.allGates r.call).length+8*r.selected.1.k+4 := by
  cases ht : r.test with
  | population =>
    simp only [MomentRequest.formula,ht]
    exact (populationMoment_syntax _ _ _ _).1.trans (by omega)
  | digit j code row =>
    simp only [MomentRequest.formula,ht]
    rw [source_digit_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j row code.val]
    exact tupleCallMomentFormula_size_le _ _ _ _ _ _ _
  | finalError j code =>
    simp only [MomentRequest.formula,ht]
    rw [source_final_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j code.val]
    exact tupleCallMomentFormula_size_le _ _ _ _ _ _ _

/-- `lem:print`, paper/paper.tex: the actual
tree weight bounds construction arithmetic only; native coefficient
widths continue to use the separately proved formal mass. -/
theorem MomentRequest.formula_weight_bound {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.formula.weight≤
      8*(1+(r.selected.1.Xmax+1)*(r.selected.1.Xmax+2+
        ((Builder.allGates r.call).length+1)^r.selected.1.Xmax*(8*r.selected.1.Xmax+3)))+1+
        8*r.selected.1.k*((Builder.allGates r.call).length*(8*(r.coefficientBits+5)+1)) := by
  cases ht : r.test with
  | population =>
    simp only [MomentRequest.formula,ht]
    have hh := (populationMoment_syntax
      (fun i : Fin (Builder.allGates r.call).length=>r.retainedWitness.getD (r.selected.1.k+i.val) false)
      0 (StagePrint.callStructural r.call r.rules r.walk 0) r.selected.1.k).2
    have hm := Nat.mul_le_mul_left (2*r.selected.1.k*(Builder.allGates r.call).length)
      (show 9≤4*(8*(r.coefficientBits+5)+1) by omega)
    have he : 2*r.selected.1.k*(Builder.allGates r.call).length*
        (4*(8*(r.coefficientBits+5)+1))=
        8*r.selected.1.k*((Builder.allGates r.call).length*(8*(r.coefficientBits+5)+1)) := by ring
    rw [he] at hm
    have hleft : 2*r.selected.1.k*(Builder.allGates r.call).length*9=
        2*r.selected.1.k*(9*(Builder.allGates r.call).length) := by ring
    rw [hleft] at hm
    exact hh.trans (by omega)
  | digit j code row =>
    simp only [MomentRequest.formula,ht]
    rw [source_digit_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j row code.val]
    exact tupleCallMomentFormula_weight_le _ _ _ _ _ _ _ _ (r.digit_leaf_bits j row)
  | finalError j code =>
    simp only [MomentRequest.formula,ht]
    rw [source_final_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j code.val]
    exact tupleCallMomentFormula_weight_le _ _ _ _ _ _ _ _ (r.final_leaf_bits j)

/-- `lem:print`, paper/paper.tex: all original
integer leaves, including signed Newton coefficients and failed-chain
offsets, have the displayed raw-codec height. -/
theorem MomentRequest.formula_constant_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    formulaConstantBits (r.selected.1.Xmax+r.coefficientBits+2) r.formula := by
  cases ht : r.test with
  | population =>
    simp only [MomentRequest.formula,ht]
    exact cert_population_constant_bits (by decide : 0<4) _ _ _ _ _ (by omega)
  | digit j code row =>
    simp only [MomentRequest.formula,ht]
    rw [source_digit_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j row code.val]
    exact tupleCallMomentFormula_constant_bits _ _ _ _ _ _ _ _ (by omega)
      (fun g=>(r.digit_leaf_bits j row g).trans (by omega))
  | finalError j code =>
    simp only [MomentRequest.formula,ht]
    rw [source_final_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j code.val]
    exact tupleCallMomentFormula_constant_bits _ _ _ _ _ _ _ _ (by omega)
      (fun g=>(r.final_leaf_bits j g).trans (by omega))

end NearQuarticWires.StageCert.Tokens
