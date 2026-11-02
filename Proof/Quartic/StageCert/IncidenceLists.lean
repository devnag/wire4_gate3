import Proof.Quartic.StageCert.IncidenceGates
import Proof.Quartic.StagePrep.CensusLists

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:cells`, paper/paper.tex: a counted original gate
list is read directly from the source call, not a supplied incidence oracle. -/
def readCoordinateGateList : St VV :=
  .seq (readListHeader gateIndex gateLength) readCoordinateGates

/-- `sec:cells`, paper/paper.tex: only the original gate-list
indices and signed-parser scratch registers change during this scan. -/
def gateListScratch : List (Fin VV) := gateLength::gateIndex::gateScratch

/-- `sec:cells` and `prop:time`, paper/paper.tex: the counted raw list yields its exact coordinate incidence. -/
theorem readCoordinateGateList_run (C : Ctx) {n : ℕ} (gs : List (NormalizedThresholdGate n)) (i : Fin n)
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hcoord : a.env coordinate=i.val)
    (hcw : C.cw.drop a.cp = listWord gateWord gs ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + (gs.flatMap gateWord).length + 2 < 2 ^ C.Wd) :
    Hs C readCoordinateGateList a (200 * (C.cw.length + 2) ^ 3) (fun b =>
      b.env censusTotal = a.env censusTotal + coordinateSum gs i ∧
      b.cp = a.cp + (listWord gateWord gs).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b gateListScratch) := by
  have hlen := len_le_of_drop hcw
  simp only [listWord, List.length_append] at hlen
  have hgs : gs.length ≤ C.cw.length := by
    have hf := length_le_flatMap gs gateWord
      (fun g => by have := arity_add_one_le_gateWord g; omega)
    omega
  have hnb : natBitLength gs.length ≤ C.cw.length :=
    (natBitLength_le_len _).trans (by omega)
  simp only [listWord, List.append_assoc] at hcw
  unfold readCoordinateGateList
  refine Hx.hs (Hs.then (readListHeader_spec C gateIndex gateLength
    (by decide) (by decide) (by decide) (by decide) a hc gs.length _ hcw hW hL)
    (fun b ⟨hbi, hbn, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbcw : C.cw.drop b.cp = gs.flatMap gateWord ++ rest := by
    rw [hbcp, ← List.drop_drop, hcw, List.drop_left]
  have hbt : b.env censusTotal = a.env censusTotal := hbfr _ (by decide)
  refine Hs.last (readCoordinateGates_run C gs i rest b hbc
    ((hbfr _ (by decide)).trans hcoord) hbi hbn hbcw hW hL
    (by rw [hbt]; exact htotal)) ?_
  rintro d ⟨hdt, hdcp, hdwq, hdout, hdc, hdfr, _, _⟩ n2 hn2
  refine ⟨⟨by rw [hdt, hbt], ?_, hdwq.trans hbwq, hdout.trans hbout, hdc,
    Fr.trans (Fr.weaken hbfr (by decide)) (Fr.weaken hdfr (by decide))⟩, ?_⟩
  · rw [hdcp, hbcp]
    simp only [listWord, List.length_append]
    omega
  · have hp := Nat.mul_le_mul_right (120 * (C.cw.length + 2) ^ 2 + 4) hgs
    nlinarith only [hn1, hn2, hp, hnb]


end NearQuarticWires.StageCert.Incidence
