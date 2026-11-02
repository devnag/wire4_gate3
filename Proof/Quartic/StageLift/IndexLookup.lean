import Proof.Quartic.StageLift.PrintRequest

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Interfaces

/-- `lem:residue` and Step 3, paper/paper.tex: the actual digit list has its literal circuit-major
finite-product ordering, not an assumed address correspondence. -/
theorem printDigitList_getElem {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (circuit : Fin 2) (row : Fin (r.child.cellCall.J + 1)) :
    (printDigitList r)[circuit.val * (r.child.cellCall.J + 1) + row.val]'(by
      rw [printDigitList_length]
      nlinarith [circuit.isLt, row.isLt]) = r.digits circuit row := by
  let L := r.child.cellCall.J + 1
  let f : Fin (2 * L) → ℤ := fun address =>
    r.digits (finProdFinEquiv.symm address).1 (finProdFinEquiv.symm address).2
  have hflat : printDigitList r = List.ofFn f := by
    rw [List.ofFn_mul]
    unfold printDigitList
    congr 1
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    have hj : j.val < L := j.isLt
    have ha : (⟨i.val * L + j.val, by nlinarith [i.isLt]⟩ : Fin (2 * L)) =
        finProdFinEquiv (i, j) := by
      apply Fin.ext
      change i.val * L + j.val = j.val + L * i.val
      ring
    simp only [f, ha, Equiv.symm_apply_apply]
  simp only [hflat, List.getElem_ofFn]
  have hr : row.val < L := row.isLt
  have ha : (⟨circuit.val * L + row.val, by nlinarith [circuit.isLt]⟩ : Fin (2 * L)) =
      finProdFinEquiv (circuit, row) := by
    apply Fin.ext
    change circuit.val * L + row.val = row.val + L * circuit.val
    ring
  change f (⟨circuit.val * L + row.val, _⟩ : Fin (2 * L)) = _
  rw [ha]
  simp only [f, Equiv.symm_apply_apply]

/-- `lem:residue` and Step 3, paper/paper.tex: a real normalized-bank record is exactly its original
digit reduced modulo the actual requested prime power. -/
theorem normalizedPrintIndex_digit {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (circuit : Fin 2) (row : Fin (r.child.cellCall.J + 1)) :
    (normalizedPrintIndex r).getD
      (10 + circuit.val * (r.child.cellCall.J + 1) + row.val) 0 =
      (r.digits circuit row % (r.prime ^ r.child.selected.1.e : ℤ)).toNat := by
  let header := [r.sign.toNat] ++ (List.ofFn r.pattern).map Bool.toNat ++ [r.prime]
  have hheader : header.length = 10 := by
    simp only [header, List.length_append, List.length_singleton, print_pattern_length]
  have hidx : circuit.val * (r.child.cellCall.J + 1) + row.val < (printDigitList r).length := by
    rw [printDigitList_length]
    nlinarith [circuit.isLt, row.isLt]
  change (header ++ (printDigitList r ++ printResidueList r).map
    (fun z : ℤ => (z % (r.prime ^ r.child.selected.1.e : ℤ)).toNat)).getD _ _ = _
  rw [List.getD_append_right _ _ _ _ (by rw [hheader]; omega), hheader]
  have hsub : 10 + circuit.val * (r.child.cellCall.J + 1) + row.val - 10 =
      circuit.val * (r.child.cellCall.J + 1) + row.val := by omega
  rw [hsub, List.map_append, List.getD_append _ _ _ _ (by simpa using hidx),
    List.getD_eq_getElem _ _ (by simpa using hidx), List.getElem_map,
    printDigitList_getElem]

/-- `lem:residue` and Step 3, paper/paper.tex: both actual score records follow the entire original
digit bank and retain precisely their raw score residues modulo q. -/
theorem normalizedPrintIndex_score {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (circuit : Fin 2) :
    (normalizedPrintIndex r).getD (10 + (printDigitList r).length + circuit.val) 0 =
      (r.residues circuit % (r.prime ^ r.child.selected.1.e : ℤ)).toNat := by
  let header := [r.sign.toNat] ++ (List.ofFn r.pattern).map Bool.toNat ++ [r.prime]
  have hheader : header.length = 10 := by
    simp only [header, List.length_append, List.length_singleton, print_pattern_length]
  change (header ++ (printDigitList r ++ printResidueList r).map
    (fun z : ℤ => (z % (r.prime ^ r.child.selected.1.e : ℤ)).toNat)).getD _ _ = _
  rw [List.getD_append_right _ _ _ _ (by rw [hheader]; omega), hheader]
  rw [List.map_append, List.getD_append_right _ _ _ _ (by simp; omega)]
  have hsub : 10 + (printDigitList r).length + circuit.val - 10 - (printDigitList r).length =
      circuit.val := by omega
  rw [List.length_map, hsub, List.getD_eq_getElem _ _ (by
    simp only [List.length_map, printResidueList_length]
    exact circuit.isLt), List.getElem_map]
  simp only [printResidueList, List.getElem_ofFn]

end NearQuarticWires.StageLift
