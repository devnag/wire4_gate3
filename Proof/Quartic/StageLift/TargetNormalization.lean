import Proof.Quartic.StageLift.SourceCarrier
import Proof.Quartic.StageLift.IndexSchema
import Mathlib.Algebra.BigOperators.ModEq

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces
open scoped BigOperators

/-- `lem:residue`, paper/paper.tex: streaming
normalization of arbitrary digit and score targets modulo p^e preserves
all original residue targets, including exact digit reduction modulo p. -/
theorem normalized_callResidueTarget (c : Call) (p : Cells.Parameters) (prime : ℕ)
    (he : 0 < p.e) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ)
    (index : Fin 2 × Option (Fin (p.J - 1 + 1))) :
    callResidueTarget c p prime (fun j i => digits j i % (prime ^ p.e : ℕ))
        (fun j => residues j % (prime ^ p.e : ℕ)) index ≡
      callResidueTarget c p prime digits residues index [ZMOD (prime ^ p.e : ℕ)] := by
  classical
  rcases index with ⟨j,i⟩
  by_cases hj : j ∈ Builder.circuitSet c
  · cases i with
    | none =>
      simpa only [callResidueTarget, if_pos hj] using
        Int.mod_modEq (residues j) ((prime ^ p.e : ℕ) : ℤ)
    | some row =>
      simp only [callResidueTarget, if_pos hj]
      rw [normalized_digit_target prime p.e he]
  · simp only [callResidueTarget, if_neg hj]
    exact Int.ModEq.refl _

/-- `imp:amp` and `lem:residue`, paper/paper.tex: the literal integer amplifier preserves every input
congruence modulo the actual prime power. -/
theorem amplifierValue_modEq (q : ℤ) (e : ℕ) (u v : ℤ) (h : u ≡ v [ZMOD q]) :
    NearCubicGates.ResidueCounts.amplifierValue e u ≡
      NearCubicGates.ResidueCounts.amplifierValue e v [ZMOD q] := by
  unfold NearCubicGates.ResidueCounts.amplifierValue
  apply (Int.ModEq.refl _).sub
  apply (((Int.ModEq.refl _).sub h).pow e).mul
  apply Int.ModEq.sum
  intro j _
  exact (Int.ModEq.refl _).mul (h.pow j)

/-- `lem:residue`, paper/paper.tex: every
integer Fermat-product source depends on its targets only modulo the
recovery modulus, independently of atom assignments or certification. -/
theorem indexedFermatFormula_targets_modEq {V J : ℕ} (q : ℤ) (prime : ℕ)
    (forms : Fin 2 × Option (Fin (J + 1)) → Formula V)
    (rho rho' : Fin 2 × Option (Fin (J + 1)) → ℤ)
    (hrho : ∀ i, rho i ≡ rho' i [ZMOD q]) (point : Fin V → ℤ) :
    (indexedFermatFormula prime forms rho).eval point ≡
      (indexedFermatFormula prime forms rho').eval point [ZMOD q] := by
  rw [indexedFermatFormula_eval, indexedFermatFormula_eval]
  unfold NearCubicGates.ResidueCounts.fermatProduct
  apply Int.ModEq.prod
  intro i _
  exact (Int.ModEq.refl _).sub (((Int.ModEq.refl _).sub (hrho i)).pow (prime - 1))

/-- `lem:print` and `lem:residue`, paper/paper.tex: the ACTUAL generated tuple source with
stream-normalized targets is congruent to the original raw-index
walk polynomial on every integer atom assignment. -/
theorem sourceWalkFormula_eval_modEq_raw {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8))
    (point : Fin (17 * (Builder.allGates r.child.call).length) → ℤ) :
    (sourceWalkFormula r index).eval point ≡
      (callResidueWalkFormula r.child.call (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2)
        r.child.witness (printWalkAt _ index) r.pattern r.prime r.digits r.residues
        (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (printWalkAt _ index))).eval point
        [ZMOD (r.prime ^ r.child.selected.1.e : ℕ)] := by
  let hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  let q := r.prime ^ r.child.selected.1.e
  let forms := callResidueForm r.child.call hs r.child.witness r.pattern
  let rho := callResidueTarget r.child.call r.child.selected.1 r.prime
    (fun j i => r.digits j i % (q : ℤ)) (fun j => r.residues j % (q : ℤ))
  let rho' := callResidueTarget r.child.call r.child.selected.1 r.prime r.digits r.residues
  have htarget : ∀ i, rho i ≡ rho' i [ZMOD (q : ℤ)] :=
    normalized_callResidueTarget r.child.call r.child.selected.1 r.prime hs.e_pos r.digits r.residues
  have hf := indexedFermatFormula_targets_modEq (q : ℤ) r.prime forms rho rho' htarget point
  have ham : (Formula.amp r.child.selected.1.e (indexedFermatFormula r.prime forms rho)).eval point ≡
      (Formula.amp r.child.selected.1.e (indexedFermatFormula r.prime forms rho')).eval point [ZMOD (q : ℤ)] := by
    simpa only [Formula.eval_amp] using amplifierValue_modEq (q : ℤ) r.child.selected.1.e _ _ hf
  change (tupleResidueWalkFormula r.child.call hs r.child.witness (printWalkAt _ index) r.pattern r.prime
    (fun j i => r.digits j i % (q : ℤ)) (fun j => r.residues j % (q : ℤ))
    (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (printWalkAt _ index))).eval point ≡ _ [ZMOD (q : ℤ)]
  rw [tupleResidueWalkFormula_eval]
  exact (Int.ModEq.refl _).mul ((Int.ModEq.refl _).mul ham)

/-- `lem:print`, paper/paper.tex: the formatter's
actual constant-normalized source retains the original raw-index
polynomial modulo q, before the native table evaluation begins. -/
theorem reduced_sourceWalkFormula_eval_modEq_raw {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8))
    (point : Fin (17 * (Builder.allGates r.child.call).length) → ℤ) :
    (reduceConstants (r.prime ^ r.child.selected.1.e) (sourceWalkFormula r index)).eval point ≡
      (callResidueWalkFormula r.child.call (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2)
        r.child.witness (printWalkAt _ index) r.pattern r.prime r.digits r.residues
        (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (printWalkAt _ index))).eval point
        [ZMOD (r.prime ^ r.child.selected.1.e : ℕ)] :=
  (reduceConstants_eval _ _ point).trans (sourceWalkFormula_eval_modEq_raw r index point)

end NearQuarticWires.StageLift
