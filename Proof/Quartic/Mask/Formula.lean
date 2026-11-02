import Proof.Quartic.Mask.Polynomial
import Proof.Gates.Tabulator.Formula

set_option autoImplicit false

namespace NearQuarticWires.Mask

open scoped BigOperators
open NearCubicGates.Close.Tabulator

/-- Paper `lem:maskpoly`: a finite exact integer formula sum. -/
def formulaListSum {V : ℕ} : List (Formula V) → Formula V
  | [] => .const 0
  | f :: fs => .add f (formulaListSum fs)

/-- Paper `lem:maskpoly`: a finite exact integer formula product. -/
def formulaListProd {V : ℕ} : List (Formula V) → Formula V
  | [] => .const 1
  | f :: fs => .mul f (formulaListProd fs)

/-- Paper `lem:maskpoly`: exact evaluation of a formula sum. -/
theorem formulaListSum_eval {V : ℕ} (fs : List (Formula V)) (β : Fin V → ℤ) :
    (formulaListSum fs).eval β = (fs.map (Formula.eval β)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [formulaListSum, Formula.eval, ih]

/-- Paper `lem:maskpoly`: exact evaluation of a formula product. -/
theorem formulaListProd_eval {V : ℕ} (fs : List (Formula V)) (β : Fin V → ℤ) :
    (formulaListProd fs).eval β = (fs.map (Formula.eval β)).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [formulaListProd, Formula.eval, ih]

/-- Paper `lem:maskpoly`: a sum never raises a uniform degree bound. -/
theorem formulaListSum_degree_le {V D : ℕ} (fs : List (Formula V))
    (h : ∀ f ∈ fs, f.degree ≤ D) : (formulaListSum fs).degree ≤ D := by
  induction fs with
  | nil => exact Nat.zero_le _
  | cons f fs ih =>
    exact max_le (h f (by simp)) (ih fun g hg => h g (by simp [hg]))

/-- Paper `lem:maskpoly`: formula product degree is the sum of
the actual factor degrees. -/
theorem formulaListProd_degree {V : ℕ} (fs : List (Formula V)) :
    (formulaListProd fs).degree = (fs.map Formula.degree).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [formulaListProd, Formula.degree, ih]

/-- Paper `lem:maskpoly`: the exact positive coefficient-mass
bound of the finite sum constructor. -/
theorem formulaListSum_mass {V : ℕ} (fs : List (Formula V)) :
    (formulaListSum fs).mass = (fs.map Formula.mass).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [formulaListSum, Formula.mass, ih]

/-- Paper `lem:maskpoly`: the exact coefficient-mass bound
of the finite product constructor. -/
theorem formulaListProd_mass {V : ℕ} (fs : List (Formula V)) :
    (formulaListProd fs).mass = (fs.map Formula.mass).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [formulaListProd, Formula.mass, ih]

/-- Paper `lem:maskpoly`: finite sum indexed by an explicit
finite occurrence or subset list. -/
noncomputable def formulaSum {ι : Type*} {V : ℕ} (s : Finset ι) (f : ι → Formula V) : Formula V :=
  formulaListSum (s.toList.map f)

/-- Paper `lem:maskpoly`: finite product over an actual
selected subset of occurrences. -/
noncomputable def formulaProd {ι : Type*} {V : ℕ} (s : Finset ι) (f : ι → Formula V) : Formula V :=
  formulaListProd (s.toList.map f)

/-- Paper `lem:maskpoly`: exact integer evaluation of the
explicit finite sum constructor used by the printer. -/
theorem formulaSum_eval {ι : Type*} {V : ℕ} (s : Finset ι) (f : ι → Formula V)
    (β : Fin V → ℤ) : (formulaSum s f).eval β = ∑ i ∈ s, (f i).eval β := by
  classical
  simp [formulaSum, formulaListSum_eval, List.map_map, Function.comp_def]

/-- Paper `lem:maskpoly`: exact integer evaluation of the
explicit finite product constructor used by the printer. -/
theorem formulaProd_eval {ι : Type*} {V : ℕ} (s : Finset ι) (f : ι → Formula V)
    (β : Fin V → ℤ) : (formulaProd s f).eval β = ∏ i ∈ s, (f i).eval β := by
  classical
  simp [formulaProd, formulaListProd_eval, List.map_map, Function.comp_def]

/-- Paper `lem:maskpoly`: the finite sum constructor preserves
the bound of every actual formula in its finite index set. -/
theorem formulaSum_degree_le {ι : Type*} {V D : ℕ} (s : Finset ι) (f : ι → Formula V)
    (h : ∀ i ∈ s, (f i).degree ≤ D) : (formulaSum s f).degree ≤ D := by
  classical
  apply formulaListSum_degree_le
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  exact h i (by simpa using hi)

/-- Paper `lem:maskpoly`: actual finite product degree. -/
theorem formulaProd_degree {ι : Type*} {V : ℕ} (s : Finset ι) (f : ι → Formula V) :
    (formulaProd s f).degree = ∑ i ∈ s, (f i).degree := by
  classical
  simp [formulaProd, formulaListProd_degree, List.map_map, Function.comp_def]

/-- Paper `lem:maskpoly`: actual finite sum coefficient mass. -/
theorem formulaSum_mass {ι : Type*} {V : ℕ} (s : Finset ι) (f : ι → Formula V) :
    (formulaSum s f).mass = ∑ i ∈ s, (f i).mass := by
  classical
  simp [formulaSum, formulaListSum_mass, List.map_map, Function.comp_def]

/-- Paper `lem:maskpoly`: actual finite product coefficient mass. -/
theorem formulaProd_mass {ι : Type*} {V : ℕ} (s : Finset ι) (f : ι → Formula V) :
    (formulaProd s f).mass = ∏ i ∈ s, (f i).mass := by
  classical
  simp [formulaProd, formulaListProd_mass, List.map_map, Function.comp_def]

/-- Paper `lem:maskpoly`: the literal printer-compatible
integer mask formula. Each `b i` is the quadratic residual-square formula. -/
noncomputable def maskFormula {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (τ Xmax : ℕ) : Formula V :=
  .mul (.const (if structural then 1 else 0))
    (formulaSum (Finset.range (Xmax + 1)) fun a =>
      .mul (.const (newtonCoeff τ a))
        (formulaSum (Finset.univ.powersetCard a) fun s => formulaProd s b))

/-- Paper `lem:maskpoly`: printer-compatible formula degree
is at most `2 Xmax` for actual quadratic residual-square inputs. -/
theorem maskFormula_degree_le {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (τ Xmax : ℕ)
    (hb : ∀ i, (b i).degree ≤ 2) :
    (maskFormula structural b τ Xmax).degree ≤ 2 * Xmax := by
  classical
  change 0 + _ ≤ _
  simp only [zero_add]
  apply formulaSum_degree_le
  intro a ha
  change 0 + _ ≤ _
  simp only [zero_add]
  apply formulaSum_degree_le
  intro s hs
  rw [formulaProd_degree]
  have hs' : s.card = a := (Finset.mem_powersetCard.mp hs).2
  calc
    _ ≤ ∑ _i ∈ s, 2 := Finset.sum_le_sum fun i _ => hb i
    _ = 2 * a := by simp [hs', mul_comm]
    _ ≤ 2 * Xmax := Nat.mul_le_mul_left _ (by simpa using ha)

/-- Paper `lem:maskpoly`: complete exact mask realization
in the printer's concrete integer `Formula V` language. -/
theorem maskFormula_eval_eq_mask {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (τ Xmax : ℕ)
    (β : Fin V → ℤ) (active : Finset ι)
    (hb : ∀ i, (b i).eval β = if i ∈ active then 1 else 0)
    (hX : active.card ≤ Xmax ∨ structural = false) :
    (maskFormula structural b τ Xmax).eval β = mask structural τ active.card := by
  classical
  have hchoose (a : ℕ) :
      (∑ s ∈ Finset.univ.powersetCard a,
        ∏ i ∈ s, (if i ∈ active then (1 : ℤ) else 0)) =
        (active.card.choose a : ℤ) := by
    simpa only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X] using
      eval_esymm_indicator active a
  have he : (maskFormula structural b τ Xmax).eval β =
      maskPolyEval structural τ Xmax active.card := by
    simp only [maskFormula, Formula.eval, formulaSum_eval, formulaProd_eval, hb, hchoose,
      maskPolyEval]
  rw [he]
  exact maskPoly_eq_mask structural τ Xmax active.card hX

/-- Paper `lem:maskpoly`, and `lem:print`: a fully
explicit coefficient-mass bound sufficient for the printer's polynomial-bit
contract. This bound deliberately allows arbitrary atom aliases; it is weaker
than the paper's sharper occurrence-separated `O(Xmax + λ_n)` bit estimate. -/
theorem maskFormula_mass_le {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (τ Xmax : ℕ)
    (hb : ∀ i, (b i).mass ≤ 16) :
    (maskFormula structural b τ Xmax).mass ≤
      (Xmax + 1) * 2 ^ Xmax * 2 ^ Fintype.card ι * 16 ^ Xmax := by
  classical
  have hstruct : (if structural then (1 : ℤ) else 0).natAbs ≤ 1 := by
    cases structural <;> decide
  change (if structural then (1 : ℤ) else 0).natAbs * _ ≤ _
  apply le_trans (Nat.mul_le_mul_right _ hstruct)
  rw [one_mul, formulaSum_mass]
  calc
    _ ≤ ∑ _a ∈ Finset.range (Xmax + 1),
        2 ^ Xmax * (2 ^ Fintype.card ι * 16 ^ Xmax) := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ≤ Xmax := by simpa using ha
      have hc : (newtonCoeff τ a).natAbs ≤ 2 ^ Xmax := by
        have hc' : (newtonCoeff τ a).natAbs ≤ 2 ^ a := by
          have hcZ := newtonCoeff_abs_le τ a
          rw [← Int.natCast_natAbs] at hcZ
          exact_mod_cast hcZ
        exact hc'.trans (Nat.pow_le_pow_right (by norm_num) ha')
      change (newtonCoeff τ a).natAbs * _ ≤ _
      apply Nat.mul_le_mul hc
      rw [formulaSum_mass]
      have hcard : (Finset.univ.powersetCard a : Finset (Finset ι)).card ≤
          2 ^ Fintype.card ι := by
        calc
          _ ≤ (Finset.univ : Finset ι).powerset.card :=
            Finset.card_le_card (fun _ hs =>
              Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hs).1)
          _ = _ := by simp
      calc
        _ ≤ ∑ _s ∈ (Finset.univ.powersetCard a : Finset (Finset ι)), 16 ^ Xmax := by
          apply Finset.sum_le_sum
          intro s hs
          rw [formulaProd_mass]
          calc
            _ ≤ ∏ _i ∈ s, 16 := Finset.prod_le_prod' fun i _ => hb i
            _ = 16 ^ a := by simp [(Finset.mem_powersetCard.mp hs).2]
            _ ≤ 16 ^ Xmax := Nat.pow_le_pow_right (by norm_num) ha'
        _ ≤ 2 ^ Fintype.card ι * 16 ^ Xmax := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact Nat.mul_le_mul_right _ hcard
    _ = _ := by simp; ring

/-- Paper `lem:maskpoly`, and `lem:print`: every
actual multilinearized coefficient of the mask has the explicit integer
bound below, including merges caused by arbitrary atom aliases. -/
theorem maskFormula_expanded_coefficient_le {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (τ Xmax : ℕ)
    (hb : ∀ i, (b i).mass ≤ 16)
    (term : Finset (Fin V) × ℤ) (ht : term ∈ (maskFormula structural b τ Xmax).expand) :
    term.2.natAbs ≤ (Xmax + 1) * 2 ^ Xmax * 2 ^ Fintype.card ι * 16 ^ Xmax :=
  (Formula.expand_coeff_le _ term ht).trans (maskFormula_mass_le structural b τ Xmax hb)

/-- Paper `lem:maskpoly`, and `lem:print`: explicit
base-two coefficient bound, valid even with arbitrary aliases of atom slots. -/
theorem maskFormula_mass_le_two_pow {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (τ Xmax : ℕ)
    (hb : ∀ i, (b i).mass ≤ 16) :
    (maskFormula structural b τ Xmax).mass ≤ 2 ^ (Fintype.card ι + 6 * Xmax) := by
  have hx : Xmax + 1 ≤ 2 ^ Xmax := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := Xmax))
  apply le_trans (maskFormula_mass_le structural b τ Xmax hb)
  calc
    _ ≤ 2 ^ Xmax * 2 ^ Xmax * 2 ^ Fintype.card ι * 16 ^ Xmax :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hx))
    _ = _ := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
      simp only [← pow_add]
      congr 1
      omega

/-- Paper `lem:maskpoly`, and `lem:print`: the
multilinearized coefficients have at most `G + 6 Xmax + 1` bits. This proves
the printer's polynomial-bit requirement with a weaker explicit estimate
than the paper's occurrence-separated sharp estimate. -/
theorem maskFormula_coefficient_bits {ι : Type*} [Fintype ι] {V : ℕ}
    (structural : Bool) (b : ι → Formula V) (τ Xmax : ℕ)
    (hb : ∀ i, (b i).mass ≤ 16)
    (term : Finset (Fin V) × ℤ) (ht : term ∈ (maskFormula structural b τ Xmax).expand) :
    Nat.size term.2.natAbs ≤ Fintype.card ι + 6 * Xmax + 1 := by
  rw [Nat.size_le]
  have hc : term.2.natAbs ≤ 2 ^ (Fintype.card ι + 6 * Xmax) :=
    (Formula.expand_coeff_le _ term ht).trans (maskFormula_mass_le_two_pow structural b τ Xmax hb)
  apply hc.trans_lt
  rw [pow_succ]
  have hp : 0 < 2 ^ (Fintype.card ι + 6 * Xmax) := by positivity
  omega

end NearQuarticWires.Mask
