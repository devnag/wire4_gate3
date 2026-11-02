import Proof.Quartic.StagePrep.CensusLists

/-!
# The physical circuit wire and unit-top census

Paper: `def:class`, paper/paper.tex, normalized calls, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces

/-- The finite unit-top test of normalized calls, `sec:counting`, paper/paper.tex. -/
instance unitTopDecidable {n : ℕ} (Cc : NCircuit n) : Decidable (Transfer.UnitTop Cc) := by
  unfold Transfer.UnitTop
  infer_instance

/-- The three literal lists of a circuit in `sec:counting`, paper/paper.tex: occurrences, top coefficients, and the full lookup table. -/
def censusCircuit : St VV := .seq countGateList (.seq checkCoefficientList pc3)

/-- Registers changed by the circuit census of
`sec:counting`, paper/paper.tex. -/
def circuitCensusT : List (Fin VV) := gateListT ++ coefficientListT ++ pc3T

/-- Reading an entire circuit of `sec:counting`, paper/paper.tex
computes its actual physical wire count and the unit-top flag,
without reading any witness bit. -/
theorem censusCircuit_spec (C : Ctx) {n : ℕ} (Cc : NCircuit n)
    (rest : List Bool) (a : DS VV) (hc : Cst a) (P0 : Prop) [Decidable P0]
    (hflag : a.env censusUnit = bnat P0)
    (hcw : C.cw.drop a.cp = circuitWord Cc ++ rest)
    (hW : 2 * C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + (circuitWord Cc).length + 2 < 2 ^ C.Wd) :
    Hs C censusCircuit a (500 * (C.cw.length + 2) ^ 3) (fun b =>
      b.env censusTotal = a.env censusTotal + Transfer.wires Cc ∧
      b.env censusUnit = bnat (P0 ∧ Transfer.UnitTop Cc) ∧
      b.cp = a.cp + (circuitWord Cc).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b circuitCensusT) := by
  have hclen : (Cc.gates.flatMap gateWord).length ≤ (circuitWord Cc).length := by
    simp only [circuitWord, listWord, List.length_append]
    omega
  simp only [circuitWord, List.append_assoc] at hcw
  unfold censusCircuit
  refine Hx.hs (Hs.then (countGateList_spec C Cc.gates
    (listWord intWord Cc.coeffs ++ listWord bitWord Cc.table ++ rest)
    a hc (by simpa only [List.append_assoc] using hcw) (by omega) hL (by omega))
    (fun b ⟨hbt, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbcw : C.cw.drop b.cp =
      listWord intWord Cc.coeffs ++ (listWord bitWord Cc.table ++ rest) := by
    rw [hbcp, ← List.drop_drop, hcw, List.drop_left]
  have hbf : b.env censusUnit = bnat P0 := (hbfr _ (by decide)).trans hflag
  refine Hs.then (checkCoefficientList_spec C Cc.coeffs _ b hbc P0 hbf hbcw
    (by omega) hL) (fun d ⟨hdf, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdcw : C.cw.drop d.cp = listWord bitWord Cc.table ++ rest := by
    rw [hdcp, ← List.drop_drop, hbcw, List.drop_left]
  refine Hs.last (pc3_spec Cc.table d hdc rest hdcw hW hL)
    (fun e ⟨_, _, hecp, hewq, heout, hec, hefr⟩ n3 hn3 => ?_)
  refine ⟨⟨?_, ?_, ?_, hewq.trans (hdwq.trans hbwq),
    heout.trans (hdout.trans hbout), hec,
    Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.trans (Fr.weaken hdfr (by decide)) (Fr.weaken hefr (by decide)))⟩, ?_⟩
  · rw [hefr _ (by decide), hdfr _ (by decide), hbt]
    rfl
  · rw [hefr _ (by decide), hdf]
    rfl
  · rw [hecp, hdcp, hbcp]
    simp only [circuitWord, List.length_append]
    omega
  · have hpow : (C.cw.length + 2) ^ 2 ≤ (C.cw.length + 2) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 1 ≤ (C.cw.length + 2) ^ 3 := Nat.pow_pos (by omega)
    omega

end NearQuarticWires.StagePrep
