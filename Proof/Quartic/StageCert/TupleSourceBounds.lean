import Proof.Quartic.StageLift.TupleSize
import Proof.Quartic.Cells.ParametersCertLeafBits

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Tabulator
open Cells.ParameterArithmetic

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: an actual guarded tuple product retains its additive
child weight and the literal zero/one ordering coefficient. -/
theorem tupleTerm_weight_le {G V a : ℕ} (b : Fin G→Formula V) (f : Fin a→Fin G)
    (B : ℕ) (hb : ∀i,(b i).weight≤B) : (tupleTerm b f).weight≤a*B+2 := by
  classical
  have hp := cert_prodList_weight_le (List.ofFn fun i : Fin a=>b (f i)) B (by
    intro F hF
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hF
    exact hb (f i))
  rw [StageLift.formula_prodList_eq] at hp
  simp only [List.length_ofFn] at hp
  have hg : Nat.size (if StrictMono f then (1:ℤ) else 0).natAbs≤1 := by split <;> decide
  change Nat.size (if StrictMono f then (1:ℤ) else 0).natAbs+_≤_
  omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual G^a radix terms and every literal carry
in their right-linear sum enter the syntactic construction bound. -/
theorem tupleElementary_weight_le {G V : ℕ} (b : Fin G→Formula V) (a B : ℕ)
    (hb : ∀i,(b i).weight≤B) : (tupleElementary b a).weight≤G^a*(a*B+3) := by
  unfold tupleElementary
  rw [←StageLift.formula_sumList_eq]
  apply (cert_sumList_weight_le _ (a*B+2) ?_).trans
  · simp only [List.length_ofFn]
    rfl
  · intro F hF
    obtain ⟨address,rfl⟩ := List.mem_ofFn.mp hF
    exact tupleTerm_weight_le b _ B hb

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the exact emitted tuple-mask syntax pays all invalid
tuples as well as signed Newton leaves; no coefficient-width claim
is inferred from this construction-weight bound. -/
theorem tupleMaskFormula_weight_le {G V : ℕ} (structural : Bool) (b : Fin G→Formula V)
    (tau X B : ℕ) (hb : ∀i,(b i).weight≤B) :
    (tupleMaskFormula structural b tau X).weight≤
      1+(X+1)*(X+2+(G+1)^X*(X*B+3)) := by
  have hi (a : ℕ) (ha : a≤X) :
      (tupleElementary b a).weight≤(G+1)^X*(X*B+3) :=
    (tupleElementary_weight_le b a B hb).trans (Nat.mul_le_mul
      ((Nat.pow_le_pow_left (Nat.le_succ G) a).trans (Nat.pow_le_pow_right (Nat.succ_pos G) ha))
      (Nat.add_le_add_right (Nat.mul_le_mul_right B ha) 3))
  have hs := cert_sumList_weight_le
    (List.ofFn fun a : Fin (X+1)=>Formula.mul (.const (Mask.newtonCoeff tau a.val))
      (tupleElementary b a.val)) (X+1+(G+1)^X*(X*B+3)) (by
    intro F hF
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hF
    have hn := (cert_newton_coefficient_bits tau a.val).trans (by omega : a.val+1≤X+1)
    exact Nat.add_le_add hn (hi a.val (by omega)))
  rw [StageLift.formula_sumList_eq] at hs
  simp only [List.length_ofFn] at hs
  have he : (X+1)*(X+1+(G+1)^X*(X*B+3)+1)=
      (X+1)*(X+2+(G+1)^X*(X*B+3)) := by ring
  rw [he] at hs
  have hg : Nat.size (if structural then (1:ℤ) else 0).natAbs≤1 := by cases structural <;> decide
  change Nat.size (if structural then (1:ℤ) else 0).natAbs+_≤_
  omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: tuple-order guards add only literal Boolean integer
leaves; all actual source child-constant bounds are preserved. -/
theorem tupleTerm_constant_bits {G V a : ℕ} (b : Fin G→Formula V)
    (f : Fin a→Fin G) (L : ℕ) (hL : 1≤L) (hb : ∀i,formulaConstantBits L (b i)) :
    formulaConstantBits L (tupleTerm b f) := by
  classical
  refine ⟨?_,?_⟩
  · change Nat.size (if StrictMono f then (1:ℤ) else 0).natAbs≤L
    split <;> simp only [Int.natAbs_zero,Int.natAbs_one,Nat.size_zero,Nat.size_one] <;> omega
  · rw [←StageLift.formula_prodList_eq]
    apply cert_prodList_constant_bits _ L hL
    intro F hF
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hF
    exact hb (f i)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the complete actual tuple-mask AST has a literal
constant-bit proof on all formal assignments and all bad columns. -/
theorem tupleMaskFormula_constant_bits {G V : ℕ} (structural : Bool) (b : Fin G→Formula V)
    (tau X L : ℕ) (hXL : X+1≤L) (hb : ∀i,formulaConstantBits L (b i)) :
    formulaConstantBits L (tupleMaskFormula structural b tau X) := by
  have hL : 1≤L := by omega
  refine ⟨?_,?_⟩
  · cases structural with
    | false => exact Nat.zero_le L
    | true => exact hL
  · rw [←StageLift.formula_sumList_eq]
    apply cert_sumList_constant_bits
    intro F hF
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hF
    refine ⟨(cert_newton_coefficient_bits tau a.val).trans (by omega),?_⟩
    unfold tupleElementary
    rw [←StageLift.formula_sumList_eq]
    apply cert_sumList_constant_bits
    intro F hF
    obtain ⟨address,rfl⟩ := List.mem_ofFn.mp hF
    exact tupleTerm_constant_bits b _ L hL hb

end NearQuarticWires.StageCert
