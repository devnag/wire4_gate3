import Proof.Quartic.StageLift.FormulaSize
import Proof.Quartic.StageLift.FormulaBytes
import Proof.Quartic.StageLift.ResidueFormula

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces

/-- `sec:walks` and `lem:print`, paper/paper.tex: original circuit-walk syntax is linear in the shared
occurrence pool, even for arbitrary signed integer weights. -/
theorem callWalkFormula_size_le (c : Call) (j : Fin 2)
    (weight : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4) :
    (StagePrint.callWalkFormula c j weight sigma).size ≤ 82 * (Builder.allGates c).length + 1 := by
  unfold StagePrint.callWalkFormula Cells.pooledWalkFormula
  simpa only [Nat.mul_comm _ 82] using
    walkFormula_size_le (StagePrint.circuitWeights c j weight)
      (fun l => Cycle.signValue (sigma l))
      (fun g e z => Cells.atomIndex (Cells.cornerRole (by norm_num : 0 < 4) e z) g)

/-- `lem:residue`, paper/paper.tex: digit and
score forms have uniform linear syntax independent of raw target values. -/
theorem callResidueForm_size_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (sigma : Cycle.SignPattern 4) (index : Fin 2 × Option (Fin (p.J - 1 + 1))) :
    (callResidueForm c hs w sigma index).size ≤ 82 * (Builder.allGates c).length + 1 := by
  unfold callResidueForm
  split
  · cases index.2 <;> exact callWalkFormula_size_le _ _ _ _
  · simp [Formula.size]

/-- `lem:residue` and `lem:print`, paper/paper.tex: the actual Fermat conjunction pays one unary exponent
per form, with no multiplication of its children's syntax sizes. -/
theorem indexedFermatFormula_size_le {V J : ℕ} (prime B : ℕ)
    (forms : Fin 2 × Option (Fin (J + 1)) → Formula V)
    (rho : Fin 2 × Option (Fin (J + 1)) → ℤ)
    (hforms : ∀ i, (forms i).size ≤ B) :
    (indexedFermatFormula prime forms rho).size ≤
      2 * (J + 2) * (B + prime + 6) + 1 := by
  unfold indexedFermatFormula
  apply (prodList_size_le _ (B + prime + 5) ?_).trans
  · simp only [List.length_map, formIndices_length]
    exact le_rfl
  · intro f hf
    obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hf
    have hi := hforms i
    simp only [Formula.size]
    omega

/-- `lem:print`, paper/paper.tex: all eight mask
copies are added in the literal syntax before native coefficient expansion. -/
theorem walkMaskFormula_size_le {V m : ℕ} (masks : Fin (2 * m) → Formula V)
    (B : ℕ) (h : ∀ i, (masks i).size ≤ B) :
    (Cells.walkMaskFormula masks).size ≤ 2 * m * (B + 1) + 1 := by
  unfold Cells.walkMaskFormula
  apply (prodList_size_le _ B ?_).trans
  · simp
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact h i

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual selected mask syntax bound retains the
entire original subset construction factor. -/
def maskSyntaxBound (G X : ℕ) : ℕ :=
  (X + 1) * ((G + 1) ^ X * (11 * X + 2) + 4) + 3

/-- `lem:print`, paper/paper.tex: the complete
walk syntax is the additive eight-mask cost and the literal duplicated
Fermat/amplifier cost, with every exponent charged in unary. -/
def residueSyntaxBound (G X J prime e : ℕ) : ℕ :=
  8 * (maskSyntaxBound G X + 1) +
    (e + 1) * (2 * (J + 2) * (82 * G + prime + 7) + e + 8) + 4

/-- `lem:print`, paper/paper.tex: the original
per-walk Formula syntax depends on occurrence/chain/exponent parameters,
not on unreduced Gamma, digit or residue integer values. -/
theorem callResidueWalkFormula_size_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ) :
    (callResidueWalkFormula c hs w walk sigma prime digits residues weight).size ≤
      residueSyntaxBound (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e := by
  have hm := walkMaskFormula_size_le
    (fun e => StagePrint.selectedMaskFormula (by norm_num : 0 < 4)
      (Builder.selection c (p := p) w) (StagePrint.callStructural c hs walk e) e p.tau p.Xmax)
    (maskSyntaxBound (Builder.allGates c).length p.Xmax)
    (fun e => selectedMask_size_le _ _ _ e _ _)
  have hf := indexedFermatFormula_size_le prime (82 * (Builder.allGates c).length + 1)
    (callResidueForm c hs w sigma) (callResidueTarget c p prime digits residues)
    (callResidueForm_size_le c hs w sigma)
  have ha := (amp_size_le p.e
    (indexedFermatFormula prime (callResidueForm c hs w sigma)
      (callResidueTarget c p prime digits residues))).trans
    (Nat.mul_le_mul_left (p.e + 1) (Nat.add_le_add_right (Nat.add_le_add_right hf _) _))
  simp only [callResidueWalkFormula, Formula.size]
  unfold residueSyntaxBound
  nlinarith

/-- `lem:print` and `prop:time`, paper/paper.tex: an explicit polynomial factor accompanies the retained
subset-construction exponent, rather than hiding it in a size assertion. -/
def residueSyntaxPolynomial (G X J prime e : ℕ) : ℕ :=
  8 * ((X + 1) * (11 * X + 6) + 4) +
    (e + 1) * (2 * (J + 2) * (82 * G + prime + 7) + e + 8) + 4

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal subset-construction size has exponent X,
with the complete multiplier displayed as a polynomial. -/
theorem residueSyntaxBound_le_polynomial (G X J prime e : ℕ) :
    residueSyntaxBound G X J prime e ≤
      residueSyntaxPolynomial G X J prime e * (G + 1) ^ X := by
  have hA : 1 ≤ (G + 1) ^ X := Nat.one_le_pow _ _ (by omega)
  have htail := Nat.mul_le_mul_left
    ((e + 1) * (2 * (J + 2) * (82 * G + prime + 7) + e + 8) + 4) hA
  unfold residueSyntaxBound residueSyntaxPolynomial maskSyntaxBound
  nlinarith

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete reduced per-walk source syntax and actual
token bytes obey the required (V+1)^(Xmax+1) construction envelope.
All raw signed coefficient and target magnitudes have disappeared. -/
theorem reduced_residue_size_bytes_bound (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (hq : 0 < prime ^ p.e)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    let V := 17 * (Builder.allGates c).length
    let F := callResidueWalkFormula c hs w walk sigma prime digits residues weight
    F.size + formulaTokenBytes (reduceConstants (prime ^ p.e) F) ≤
      (formulaByteFactor V (prime ^ p.e) + 1) *
        residueSyntaxPolynomial (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e *
        (V + 1) ^ (p.Xmax + 1) := by
  dsimp only
  let F := callResidueWalkFormula c hs w walk sigma prime digits residues weight
  let G := (Builder.allGates c).length
  have hsize := (callResidueWalkFormula_size_le c hs w walk sigma prime digits residues weight).trans
    (residueSyntaxBound_le_polynomial G p.Xmax (p.J - 1) prime p.e)
  have hbytes := reduced_formula_token_bytes (prime ^ p.e) hq F
  have hpower : (G + 1) ^ p.Xmax ≤ (17 * G + 1) ^ (p.Xmax + 1) :=
    (Nat.pow_le_pow_left (by omega : G + 1 ≤ 17 * G + 1) p.Xmax).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    F.size + formulaTokenBytes (reduceConstants (prime ^ p.e) F) ≤
        (formulaByteFactor (17 * G) (prime ^ p.e) + 1) * F.size := by nlinarith
    _ ≤ (formulaByteFactor (17 * G) (prime ^ p.e) + 1) *
        (residueSyntaxPolynomial G p.Xmax (p.J - 1) prime p.e * (G + 1) ^ p.Xmax) :=
      Nat.mul_le_mul_left _ hsize
    _ ≤ _ := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hpower

end NearQuarticWires.StageLift
