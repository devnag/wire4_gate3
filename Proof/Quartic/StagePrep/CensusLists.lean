import Proof.Quartic.StagePrep.ListHeader
import Proof.Quartic.StagePrep.CensusGates
import Proof.Quartic.StagePrep.CensusCoefficients

/-!
# Encoded gate and coefficient lists

Paper: `def:class`, paper/paper.tex, normalized calls, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicWires.RepairRepresentation (natWord)

/-- The literal gate-list census of `def:class`, paper/paper.tex. -/
def countGateList : St VV :=
  .seq (readListHeader gateIndex gateLength) countGates

/-- Registers changed by the gate-list census of
`def:class`, paper/paper.tex. -/
def gateListT : List (Fin VV) := gateLength :: gateIndex :: gateCensusT

/-- The entire encoded occurrence list of `def:class`,
paper/paper.tex, is read in polynomial time. -/
theorem countGateList_spec (C : Ctx) {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hcw : C.cw.drop a.cp = listWord gateWord gs ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + (gs.flatMap gateWord).length + 2 < 2 ^ C.Wd) :
    Hs C countGateList a (200 * (C.cw.length + 2) ^ 3) (fun b =>
      b.env censusTotal = a.env censusTotal + gateChargeSum gs ∧
      b.cp = a.cp + (listWord gateWord gs).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b gateListT) := by
  have hlen := len_le_of_drop hcw
  simp only [listWord, List.length_append] at hlen
  have hgs : gs.length ≤ C.cw.length := by
    have hf := length_le_flatMap gs gateWord
      (fun g => by have := arity_add_one_le_gateWord g; omega)
    omega
  have hnb : natBitLength gs.length ≤ C.cw.length :=
    (natBitLength_le_len _).trans (by omega)
  simp only [listWord, List.append_assoc] at hcw
  unfold countGateList
  refine Hx.hs (Hs.then (readListHeader_spec C gateIndex gateLength
    (by decide) (by decide) (by decide) (by decide) a hc gs.length _ hcw hW hL)
    (fun b ⟨hbi, hbn, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbcw : C.cw.drop b.cp = gs.flatMap gateWord ++ rest := by
    rw [hbcp, ← List.drop_drop, hcw, List.drop_left]
  have hbt : b.env censusTotal = a.env censusTotal := hbfr _ (by decide)
  refine Hs.last (countGates_spec C gs rest b hbc hbi hbn hbcw hW hL
    (by rw [hbt]; exact htotal)) ?_
  rintro d ⟨hdt, hdcp, hdwq, hdout, hdc, hdfr, _, _⟩ n2 hn2
  refine ⟨⟨by rw [hdt, hbt], ?_, hdwq.trans hbwq, hdout.trans hbout, hdc,
    Fr.trans (Fr.weaken hbfr (by decide)) (Fr.weaken hdfr (by decide))⟩, ?_⟩
  · rw [hdcp, hbcp]
    simp only [listWord, List.length_append]
    omega
  · have hp := Nat.mul_le_mul_right (120 * (C.cw.length + 2) ^ 2 + 4) hgs
    nlinarith only [hn1, hn2, hp, hnb]

/-- The literal top-coefficient-list test of normalized calls,
`sec:counting`, paper/paper.tex. -/
def checkCoefficientList : St VV :=
  .seq (readListHeader weightIndex weightLength) checkCoefficients

/-- Registers changed by the top-coefficient test of
`sec:counting`, paper/paper.tex. -/
def coefficientListT : List (Fin VV) :=
  weightLength :: weightIndex :: censusUnit :: readIntT

/-- The entire top-coefficient list of normalized calls,
`sec:counting`, paper/paper.tex, is checked in polynomial time. -/
theorem checkCoefficientList_spec (C : Ctx) (cs : List ℤ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (P0 : Prop) [Decidable P0]
    (hflag : a.env censusUnit = bnat P0)
    (hcw : C.cw.drop a.cp = listWord intWord cs ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C checkCoefficientList a (100 * (C.cw.length + 2) ^ 2) (fun b =>
      b.env censusUnit = bnat (P0 ∧ ∀ z ∈ cs, z = 1) ∧
      b.cp = a.cp + (listWord intWord cs).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b coefficientListT) := by
  have hlen := len_le_of_drop hcw
  simp only [listWord, List.length_append] at hlen
  have hcs : cs.length ≤ C.cw.length := by
    have hf := length_le_flatMap cs intWord intWord_len_pos
    omega
  have hnb : natBitLength cs.length ≤ C.cw.length :=
    (natBitLength_le_len _).trans (by omega)
  simp only [listWord, List.append_assoc] at hcw
  unfold checkCoefficientList
  refine Hx.hs (Hs.then (readListHeader_spec C weightIndex weightLength
    (by decide) (by decide) (by decide) (by decide) a hc cs.length _ hcw hW hL)
    (fun b ⟨hbi, hbn, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbcw : C.cw.drop b.cp = cs.flatMap intWord ++ rest := by
    rw [hbcp, ← List.drop_drop, hcw, List.drop_left]
  have hbf : b.env censusUnit = bnat P0 := (hbfr _ (by decide)).trans hflag
  refine Hs.last (checkCoefficients_spec C cs rest b hbc P0 hbf hbi hbn hbcw hW hL) ?_
  rintro d ⟨hdf, hdcp, hdwq, hdout, hdc, hdfr, _, _⟩ n2 hn2
  refine ⟨⟨hdf, ?_, hdwq.trans hbwq, hdout.trans hbout, hdc,
    Fr.trans (Fr.weaken hbfr (by decide)) (Fr.weaken hdfr (by decide))⟩, ?_⟩
  · rw [hdcp, hbcp]
    simp only [listWord, List.length_append]
    omega
  · have hp := Nat.mul_le_mul_right (60 * C.cw.length + 78) hcs
    nlinarith only [hn1, hn2, hp, hnb]

end NearQuarticWires.StagePrep
