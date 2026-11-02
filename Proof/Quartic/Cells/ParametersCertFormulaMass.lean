import Proof.Quartic.StagePrint.BuilderMoments
import Proof.Quartic.Cells.ParametersCertificateBits
import Proof.Gates.Expand.Machine

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: coefficient mass
adds across the literal right-associated formula sum. -/
theorem formula_sumList_mass {V : ℕ} (fs : List (Formula V)) :
    (Formula.sumList fs).mass = (fs.map Formula.mass).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [Formula.sumList, Formula.mass, ih]

/-- `lem:print`, paper/paper.tex: coefficient mass
multiplies across the literal right-associated formula product. -/
theorem formula_prodList_mass {V : ℕ} (fs : List (Formula V)) :
    (Formula.prodList fs).mass = (fs.map Formula.mass).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [Formula.prodList, Formula.mass, ih]

/-- `sec:cells` and `lem:print`, paper/paper.tex: the formal four-corner difference has mass four,
independently of which Boolean assignments come from a column. -/
theorem delta_formula_mass {V : ℕ} (corners : Fin 4 → Fin V) :
    (deltaFormula corners).mass = 4 := rfl

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: each selected residual square has mass at most16. -/
theorem selected_square_mass_le {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (e : Fin (2 * m)) (g : Fin G) :
    (StagePrint.selectedSquare hm selection e g).mass ≤ 16 := by
  unfold StagePrint.selectedSquare
  split <;> simp [Formula.mass, edgeFormula, delta_formula_mass]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the literal mask's formal coefficient mass has
polynomial binary height even for arbitrary atom assignments. -/
theorem selected_mask_mass_bound {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (structural : Bool) (e : Fin (2 * m)) (tau X : ℕ) :
    (StagePrint.selectedMaskFormula hm selection structural e tau X).mass ≤ 2 ^ (G + 6 * X) := by
  simpa only [StagePrint.selectedMaskFormula, Fintype.card_fin] using Mask.maskFormula_mass_le_two_pow structural
    (StagePrint.selectedSquare hm selection e) tau X (selected_square_mass_le hm selection e)

/-- `sec:walks` and `lem:print`, paper/paper.tex: the actual linear walk formula has mass bounded by
four times the number of signed weighted edge occurrences. -/
theorem pooled_walk_formula_mass_le {m G : ℕ} (hm : 0 < m)
    (weight : Fin G → ℤ) (sign : Fin (2 * m) → ℤ) (B : ℕ)
    (hw : ∀ g, (weight g).natAbs ≤ B) (hs : ∀ e, (sign e).natAbs ≤ 1) :
    (pooledWalkFormula hm weight sign).mass ≤ 8 * m * G * B := by
  simp only [pooledWalkFormula, walkFormula, formula_sumList_mass,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, Formula.mass,
    Int.natAbs_mul, delta_formula_mass]
  calc
    (∑ g, ∑ e, (weight g).natAbs * (sign e).natAbs * 4) ≤
        ∑ _g : Fin G, ∑ _e : Fin (2 * m), B * 1 * 4 := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro e _
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (hw g) (hs e))
    _ = _ := by simp; ring

/-- `lem:print`, paper/paper.tex: the formal mass
of a complete eighth-order masked moment uses eight mask masses
and the literal linear-form mass to the power8k. -/
theorem moment_formula_mass_le {V : ℕ} (masks : Fin 8 → Formula V)
    (form : Formula V) (G X k B : ℕ)
    (hm : ∀ e, (masks e).mass ≤ 2 ^ (G + 6 * X))
    (hf : form.mass ≤ 32 * G * B) :
    (momentWalkFormula (m := 4) masks form k).mass ≤
      2 ^ (8 * (G + 6 * X)) * (32 * G * B) ^ (8 * k) := by
  have hp : (walkMaskFormula (m := 4) masks).mass ≤ (2 ^ (G + 6 * X)) ^ 8 := by
    simp only [walkMaskFormula, formula_prodList_mass, List.map_ofFn, List.prod_ofFn]
    calc
      (∏ e, (masks e).mass) ≤ ∏ _e : Fin 8, 2 ^ (G + 6 * X) :=
        Finset.prod_le_prod' (fun e _ => hm e)
      _ = _ := by simp
  change (walkMaskFormula (m := 4) masks).mass * form.mass ^ (8 * k) ≤ _
  have hh := Nat.mul_le_mul hp (Nat.pow_le_pow_left hf (8 * k))
  simpa only [← pow_mul, Nat.mul_comm (G + 6 * X) 8] using hh

/-- `eq:testX` and `lem:print`, paper/paper.tex: the literal population AST has mass at most16G. -/
theorem selected_population_mass_le {m G : ℕ} (hm : 0 < m) (selection : Fin G → Bool)
    (e : Fin (2 * m)) :
    (StagePrint.selectedPopulationFormula hm selection e).mass ≤ 16 * G := by
  simp only [StagePrint.selectedPopulationFormula, formula_sumList_mass, List.map_ofFn, List.sum_ofFn]
  calc
    (∑ g, (StagePrint.selectedSquare hm selection e g).mass) ≤ ∑ _g : Fin G, 16 :=
      Finset.sum_le_sum (fun g _ => selected_square_mass_le hm selection e g)
    _ = _ := by simp; omega

/-- `eq:testX` and `lem:print`, paper/paper.tex: the complete structural population moment has
uniform formal mass, without assuming a column passes any test. -/
theorem selected_population_moment_mass_le {m G : ℕ} (hm : 0 < m)
    (selection : Fin G → Bool) (e : Fin (2 * m)) (structural : Bool) (k : ℕ) :
    (StagePrint.selectedPopulationMomentFormula hm selection e structural k).mass ≤
      (16 * G) ^ (2 * k) := by
  have hp := Nat.pow_le_pow_left (selected_population_mass_le hm selection e) (2 * k)
  cases structural with
  | false => simp [StagePrint.selectedPopulationMomentFormula, Formula.mass]
  | true => simpa [StagePrint.selectedPopulationMomentFormula, Formula.mass] using hp

/-- `eq:testE`, `eq:testPhi` and `prop:time`, paper/paper.tex: the formal coefficient mass has
the common polynomial binary envelope, independently of syntax weight. -/
theorem certificate_formal_moment_mass_bound (E G X k B : ℕ)
    (hG : G ≤ E) (hX : X ≤ E) (hk : k ≤ E) (hB : B ≤ 2 ^ (E + 2)) :
    2 ^ (8 * (G + 6 * X)) * (32 * G * B) ^ (8 * k) ≤
      2 ^ certificateBitEnvelope E := by
  have hlinear : 32 * G * B ≤ 2 ^ (2 * E + 7) := by
    calc
      _ ≤ 32 * 2 ^ E * 2 ^ (E + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (hG.trans Nat.lt_two_pow_self.le)) hB
      _ = _ := by rw [pow_add, pow_add]; norm_num; ring
  calc
    _ ≤ 2 ^ (56 * E) * (2 ^ (2 * E + 7)) ^ (8 * k) := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_left hlinear _)
    _ = 2 ^ (56 * E + (2 * E + 7) * (8 * k)) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hh := Nat.mul_le_mul_left (2 * E + 7) (Nat.mul_le_mul_left 8 hk)
      unfold certificateBitEnvelope
      nlinarith only [hh, Nat.zero_le E]

/-- `lem:print` and `prop:time`, paper/paper.tex: every coefficient emitted by the actual expansion
machine fits the formal mass envelope and one strict extra bit. -/
theorem actual_expansion_coefficient_bits {V : ℕ} (F : Formula V) (H : ℕ)
    (hF : F.mass ≤ 2 ^ H) (term : Finset (Fin V) × ℤ)
    (ht : term ∈ NearCubicGates.Close.Expand.expansionMachine.expand ⟨V, F⟩) :
    term.2.natAbs < 2 ^ (H + 1) ∧ Nat.size term.2.natAbs ≤ H + 1 := by
  have hmass := (NearCubicGates.Close.Expand.expansionMachine.ok ⟨V, F⟩).mass
  have hcoeff := (Terms.coeff_le_absSum _ term ht).trans (hmass.trans hF)
  have hh : term.2.natAbs < 2 ^ (H + 1) := hcoeff.trans_lt
    (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self H))
  exact ⟨hh, Nat.size_le.mpr hh⟩

end NearQuarticWires.Cells.ParameterArithmetic
