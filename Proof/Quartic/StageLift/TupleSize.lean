import Proof.Quartic.StageLift.FormulaSize
import Proof.Quartic.StageCert.TupleMask

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a literal increasing-tuple flag adds two syntax nodes
to its retained occurrence product, including every invalid tuple. -/
theorem tupleTerm_size_le {G V a : ℕ} (b : Fin G → Formula V)
    (f : Fin a → Fin G) (B : ℕ) (hb : ∀ i, (b i).size ≤ B) :
    (StageCert.tupleTerm b f).size ≤ a * (B + 1) + 3 := by
  have hp := formulaListProd_size_le (List.ofFn (fun i : Fin a => b (f i))) B (by
    intro F hF
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hF
    exact hb (f i))
  simp only [List.length_ofFn] at hp
  simp only [StageCert.tupleTerm, Formula.size]
  omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: arithmetic radix enumeration charges all G^a actual
tuple terms, rather than assuming an unimplemented subset iterator. -/
theorem tupleElementary_size_le {G V : ℕ} (b : Fin G → Formula V)
    (a B : ℕ) (hb : ∀ i, (b i).size ≤ B) :
    (StageCert.tupleElementary b a).size ≤ G ^ a * (a * (B + 1) + 4) + 1 := by
  unfold StageCert.tupleElementary
  apply (formulaListSum_size_le _ (a * (B + 1) + 3) ?_).trans
  · simp
  · intro F hF
    obtain ⟨address, rfl⟩ := List.mem_ofFn.mp hF
    exact tupleTerm_size_le b (StageCert.tupleAddressEquiv G a address) B hb

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual executable tuple-mask AST retains its full
construction cost. This bound does not assert equality with the powerset AST. -/
theorem tupleMaskFormula_size_le {G V : ℕ} (structural : Bool) (b : Fin G → Formula V)
    (tau Xmax B : ℕ) (hb : ∀ i, (b i).size ≤ B) :
    (StageCert.tupleMaskFormula structural b tau Xmax).size ≤
      (Xmax + 1) * ((G + 1) ^ Xmax * (Xmax * (B + 1) + 4) + 4) + 3 := by
  have hi (a : ℕ) (ha : a ≤ Xmax) :
      (StageCert.tupleElementary b a).size ≤
        (G + 1) ^ Xmax * (Xmax * (B + 1) + 4) + 1 := by
    apply (tupleElementary_size_le b a B hb).trans
    have hp : G ^ a ≤ (G + 1) ^ Xmax :=
      (Nat.pow_le_pow_left (by omega : G ≤ G + 1) a).trans
        (Nat.pow_le_pow_right (by omega) ha)
    exact Nat.add_le_add_right
      (Nat.mul_le_mul hp (Nat.add_le_add_right (Nat.mul_le_mul_right _ ha) _)) _
  have hs := formulaListSum_size_le
    (List.ofFn (fun a : Fin (Xmax + 1) => Formula.mul
      (.const (Mask.newtonCoeff tau a.val)) (StageCert.tupleElementary b a.val)))
    ((G + 1) ^ Xmax * (Xmax * (B + 1) + 4) + 3) (by
      intro F hF
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hF
      have h := hi a.val (by omega)
      simp only [Formula.size]
      omega)
  simp only [List.length_ofFn] at hs
  simp only [StageCert.tupleMaskFormula, Formula.size]
  convert Nat.add_le_add_left hs 2 using 1 <;> ring

/-- `lem:print`, paper/paper.tex: the executable
original-pool mask's syntactic exponent matches its real G^a tuple stream,
with invalid tuples and unary square exponents fully charged. -/
theorem selectedTupleMask_size_le {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (structural : Bool) (edge : Fin (2 * m)) (tau Xmax : ℕ) :
    (StageCert.tupleMaskFormula structural (StagePrint.selectedSquare hm selection edge)
      tau Xmax).size ≤
      (Xmax + 1) * ((G + 1) ^ Xmax * (11 * Xmax + 4) + 4) + 3 := by
  simpa only [Nat.mul_comm Xmax 11] using
    tupleMaskFormula_size_le structural (StagePrint.selectedSquare hm selection edge) tau Xmax 10
      (selectedSquare_size_le hm selection edge)

end NearQuarticWires.StageLift
