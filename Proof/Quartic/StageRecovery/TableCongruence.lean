import Proof.Quartic.StageRecovery.Coefficients
import Proof.Quartic.Walks.Residue

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: the native dominance
table is the exact list sum over physical cut occurrences. -/
theorem cutTable_eq_sum (r : MatrixScoreBatch.Request) (i j : Fin r.U) :
    StagePrint.cutTable r i j =
      (r.cuts.map (fun c => cutValue c (r.phi i.val) (r.phi j.val))).sum := by
  unfold StagePrint.cutTable NearCubicWires.SupplierPrinter.weightedDominance
  unfold MatrixScoreBatch.weight MatrixScoreBatch.leftScore MatrixScoreBatch.rightScore
  rw [← List.sum_ofFn]
  have hmap :
      (List.ofFn fun k : Fin r.cuts.length =>
        cutValue (r.cuts.get k) (r.phi i.val) (r.phi j.val)) =
      r.cuts.map (fun c => cutValue c (r.phi i.val) (r.phi j.val)) := by
    change List.ofFn ((fun c => cutValue c (r.phi i.val) (r.phi j.val)) ∘ r.cuts.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  exact congrArg List.sum hmap

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the actual reduced native matrix table is congruent entry by entry to
the original signed cut table, with the same center ordering. -/
theorem reduceRequest_table_mod (r : MatrixScoreBatch.Request)
    (modulus width : ℕ) (hp : r.p ≤ width) (hm : 0 < modulus)
    (hfit : modulus ≤ 2 ^ width) (i j : Fin r.U) :
    StagePrint.cutTable (reduceRequest r modulus width hp hm hfit) i j % (modulus : ℤ) =
      StagePrint.cutTable r i j % (modulus : ℤ) := by
  rw [cutTable_eq_sum, cutTable_eq_sum]
  exact reduceCuts_sum_mod modulus r.cuts (r.phi i.val) (r.phi j.val)

/-- `lem:residue`, paper/paper.tex: centered decoding depends
only on the exact residue, including the positive even-modulus endpoint. -/
theorem centeredResidue_of_emod_eq (modulus a b : ℤ)
    (h : a % modulus = b % modulus) :
    Walks.centeredResidue modulus a = Walks.centeredResidue modulus b := by
  unfold Walks.centeredResidue
  congr 1
  exact Int.add_emod_eq_add_emod_right _ h

/-- `lem:print`, paper/paper.tex: the coefficient-reduced
native table yields exactly the centered table required by recovery. -/
theorem reduceRequest_centered_table (r : MatrixScoreBatch.Request)
    (modulus width : ℕ) (hp : r.p ≤ width) (hm : 0 < modulus)
    (hfit : modulus ≤ 2 ^ width) (i j : Fin r.U) :
    Walks.centeredResidue modulus
        (StagePrint.cutTable (reduceRequest r modulus width hp hm hfit) i j) =
      Walks.centeredResidue modulus (StagePrint.cutTable r i j) :=
  centeredResidue_of_emod_eq _ _ _ (reduceRequest_table_mod r modulus width hp hm hfit i j)

end NearQuarticWires.StageRecovery
