import Proof.Quartic.StageLift.TupleSize
import Proof.Quartic.StageLift.ResidueSize
import Proof.Quartic.StageLift.ResidueBounds

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces
open scoped BigOperators

/-- `lem:print`, paper/paper.tex: the residue source
uses the literal radix-enumerated mask emitted by the integer serializer. -/
noncomputable def tupleResidueWalkFormula (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ) : Formula (17 * (Builder.allGates c).length) :=
  .mul (.const weight) (.mul
    (Cells.walkMaskFormula (fun e => StageCert.tupleMaskFormula
      (StagePrint.callStructural c hs walk e)
      (StagePrint.selectedSquare (by norm_num : 0 < 4) (Builder.selection c (p := p) w) e)
      p.tau p.Xmax))
    (Formula.amp p.e (indexedFermatFormula prime (callResidueForm c hs w sigma)
      (callResidueTarget c p prime digits residues))))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: tuple enumeration preserves the original summand on
every integer atom assignment, without identifying the two syntax trees. -/
theorem tupleResidueWalkFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ)
    (point : Fin (17 * (Builder.allGates c).length) → ℤ) :
    (tupleResidueWalkFormula c hs w walk sigma prime digits residues weight).eval point =
      (callResidueWalkFormula c hs w walk sigma prime digits residues weight).eval point := by
  simp only [tupleResidueWalkFormula, callResidueWalkFormula, Formula.eval,
    Cells.walkMaskFormula_eval]
  congr 2
  apply Finset.prod_congr rfl
  intro e _
  exact StageCert.tupleMaskFormula_eval _ _ _ _ point

/-- `lem:print`, paper/paper.tex: the executable
tuple source retains the unchanged selected quartic degree header. -/
theorem tupleResidueWalkFormula_degree (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ) :
    (tupleResidueWalkFormula c hs w walk sigma prime digits residues weight).degree ≤
      residueDegreeBound p prime := by
  simp only [tupleResidueWalkFormula, Formula.degree, zero_add, residueDegreeBound]
  apply Nat.add_le_add
  · exact Cells.walkMaskFormula_degree _ (fun e => StageCert.tupleMaskFormula_degree_le
      _ _ _ _ (StagePrint.selectedSquare_degree (by norm_num : 0 < 4) _ e))
  · apply (Formula.degree_amp_le _ _).trans
    have h := Nat.mul_le_mul_left (2 * p.e - 1)
      (indexedFermatFormula_degree prime (callResidueForm c hs w sigma)
        (callResidueTarget c p prime digits residues) (callResidueForm_degree c hs w sigma))
    simpa only [Nat.mul_assoc] using h

/-- `lem:residue` and `lem:print`, paper/paper.tex: normalization of the emitted tuple source preserves
the original summand modulo the actual prime power. -/
theorem reduced_tupleResidueWalkFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ)
    (point : Fin (17 * (Builder.allGates c).length) → ℤ) :
    (reduceConstants (prime ^ p.e)
      (tupleResidueWalkFormula c hs w walk sigma prime digits residues weight)).eval point ≡
      (callResidueWalkFormula c hs w walk sigma prime digits residues weight).eval point
        [ZMOD (prime ^ p.e : ℕ)] := by
  rw [← tupleResidueWalkFormula_eval c hs w walk sigma prime digits residues weight point]
  exact reduceConstants_eval _ _ _

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: retaining invalid tuples increases the displayed mask
syntax multiplier by at most two. -/
theorem selectedTupleMask_size_le_twice {m G : ℕ} (hm : 0 < m)
    (selection : Fin G → Bool) (structural : Bool) (edge : Fin (2 * m)) (tau X : ℕ) :
    (StageCert.tupleMaskFormula structural (StagePrint.selectedSquare hm selection edge)
      tau X).size ≤ 2 * maskSyntaxBound G X := by
  apply (selectedTupleMask_size_le hm selection structural edge tau X).trans
  have hi := Nat.mul_le_mul_left ((G + 1) ^ X)
    (show 11 * X + 4 ≤ 2 * (11 * X + 2) by omega)
  have hj := Nat.mul_le_mul_left (X + 1)
    (show (G + 1) ^ X * (11 * X + 4) + 4 ≤
      2 * ((G + 1) ^ X * (11 * X + 2) + 4) by nlinarith)
  unfold maskSyntaxBound
  nlinarith

/-- `lem:print`, paper/paper.tex: the exact tuple
AST pays the eight additive mask copies and the original Fermat/BT syntax. -/
theorem tupleResidueWalkFormula_size_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ) :
    (tupleResidueWalkFormula c hs w walk sigma prime digits residues weight).size ≤
      2 * residueSyntaxBound (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e := by
  have hm := walkMaskFormula_size_le
    (fun e => StageCert.tupleMaskFormula (StagePrint.callStructural c hs walk e)
      (StagePrint.selectedSquare (by norm_num : 0 < 4) (Builder.selection c (p := p) w) e)
      p.tau p.Xmax)
    (2 * maskSyntaxBound (Builder.allGates c).length p.Xmax)
    (fun e => selectedTupleMask_size_le_twice _ _ _ e _ _)
  have hf := indexedFermatFormula_size_le prime (82 * (Builder.allGates c).length + 1)
    (callResidueForm c hs w sigma) (callResidueTarget c p prime digits residues)
    (callResidueForm_size_le c hs w sigma)
  have ha := (amp_size_le p.e
    (indexedFermatFormula prime (callResidueForm c hs w sigma)
      (callResidueTarget c p prime digits residues))).trans
    (Nat.mul_le_mul_left (p.e + 1) (Nat.add_le_add_right (Nat.add_le_add_right hf _) _))
  simp only [tupleResidueWalkFormula, Formula.size]
  unfold residueSyntaxBound
  nlinarith

/-- `lem:print` and `prop:time`, paper/paper.tex: actual tuple-source size and normalized bytes obey the
same construction exponent with the explicit doubled polynomial factor. -/
theorem reduced_tuple_residue_size_bytes_bound (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (hq : 0 < prime ^ p.e)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    let V := 17 * (Builder.allGates c).length
    let F := tupleResidueWalkFormula c hs w walk sigma prime digits residues weight
    F.size + formulaTokenBytes (reduceConstants (prime ^ p.e) F) ≤
      2 * (formulaByteFactor V (prime ^ p.e) + 1) *
        residueSyntaxPolynomial (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e *
        (V + 1) ^ (p.Xmax + 1) := by
  dsimp only
  let F := tupleResidueWalkFormula c hs w walk sigma prime digits residues weight
  let G := (Builder.allGates c).length
  have hsize := (tupleResidueWalkFormula_size_le c hs w walk sigma prime digits residues weight).trans
    (Nat.mul_le_mul_left 2 (residueSyntaxBound_le_polynomial G p.Xmax (p.J - 1) prime p.e))
  have hbytes := reduced_formula_token_bytes (prime ^ p.e) hq F
  have hpower : (G + 1) ^ p.Xmax ≤ (17 * G + 1) ^ (p.Xmax + 1) :=
    (Nat.pow_le_pow_left (by omega : G + 1 ≤ 17 * G + 1) p.Xmax).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    F.size + formulaTokenBytes (reduceConstants (prime ^ p.e) F) ≤
        (formulaByteFactor (17 * G) (prime ^ p.e) + 1) * F.size := by nlinarith
    _ ≤ (formulaByteFactor (17 * G) (prime ^ p.e) + 1) *
        (2 * (residueSyntaxPolynomial G p.Xmax (p.J - 1) prime p.e * (G + 1) ^ p.Xmax)) :=
      Nat.mul_le_mul_left _ hsize
    _ = 2 * (formulaByteFactor (17 * G) (prime ^ p.e) + 1) *
        residueSyntaxPolynomial G p.Xmax (p.J - 1) prime p.e * (G + 1) ^ p.Xmax := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hpower

end NearQuarticWires.StageLift
