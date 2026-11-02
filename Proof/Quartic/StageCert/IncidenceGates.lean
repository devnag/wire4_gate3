import Proof.Quartic.StageCert.IncidenceGate
import Proof.Quartic.StagePrep.CensusGates

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `sec:cells`, paper/paper.tex: an occurrence-preserving
coordinate incidence sum on the original raw gate list. -/
def coordinateSum {n : ℕ} (gs : List (NormalizedThresholdGate n)) (i : Fin n) : ℕ :=
  (gs.map (fun g => wireBit (g.weight i))).sum

/-- `sec:cells`, paper/paper.tex: one coordinate's incidence
never exceeds the full physical raw-gate charge. -/
theorem coordinateSum_le_charge {n : ℕ} (gs : List (NormalizedThresholdGate n)) (i : Fin n) :
    coordinateSum gs i≤gateChargeSum gs := by
  induction gs with
  | nil => simp [coordinateSum,gateChargeSum]
  | cons g gs ih =>
    have h : wireBit (g.weight i)≤1 := by unfold wireBit; split_ifs <;> omega
    simp only [coordinateSum,List.map_cons,List.sum_cons,gateChargeSum] at *
    omega

/-- `sec:cells`, paper/paper.tex: a new occurrence adds its
literal nonzero-coordinate contribution, retaining duplicate raw gates. -/
theorem coordinateSum_take_succ {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (i : Fin n) (k : ℕ) (hk : k<gs.length) :
    coordinateSum (gs.take (k+1)) i=coordinateSum (gs.take k) i+wireBit (gs[k].weight i) := by
  change ((gs.take (k+1)).map (fun g => wireBit (g.weight i))).sum=
    ((gs.take k).map (fun g => wireBit (g.weight i))).sum+wireBit (gs[k].weight i)
  rw [List.take_add_one,List.getElem?_eq_getElem hk]
  simp only [Option.toList,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]

/-- `sec:cells`, paper/paper.tex: the physical occurrence
loop computes coordinate incidence on the complete original gate list. -/
def readCoordinateGates : St VV :=
  .loop (.lt gateIndex gateLength) (.seq readCoordinateGate (.op (.inc gateIndex)))

/-- `sec:cells` and `prop:time`, paper/paper.tex: all original occurrences are scanned, with their exact call-word
cursor and polynomial binary cost. -/
theorem readCoordinateGates_run (C : Ctx) {n : ℕ} (gs : List (NormalizedThresholdGate n)) (i : Fin n)
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hcoord : a.env coordinate=i.val) (hi : a.env gateIndex = 0) (hn : a.env gateLength = gs.length)
    (hcw : C.cw.drop a.cp = gs.flatMap gateWord ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + (gs.flatMap gateWord).length + 2 < 2 ^ C.Wd) :
    Hs C readCoordinateGates a (gs.length * (120 * (C.cw.length + 2) ^ 2 + 4) + 2)
      (fun b => b.env censusTotal = a.env censusTotal + coordinateSum gs i ∧
        b.cp = a.cp + (gs.flatMap gateWord).length ∧
        b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
        Fr a b (gateIndex :: gateScratch) ∧
        b.env gateIndex = gs.length ∧ b.env gateLength = gs.length) := by
  let T := gateIndex :: gateScratch
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env censusTotal = a.env censusTotal + coordinateSum (gs.take k) i ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b T
  have hp : ∀ k b v, P k b → P k (b.set gateIndex v) := by
    rintro k b v ⟨hb, hw, ho, hc', hfr⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb, hw, ho,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.pos⟩,
      Fr.trans hfr (Fr.set _ _ (by decide))⟩
  have hbody : ∀ k (hk : k < gs.length) (b : DS VV), P k b →
      b.env gateIndex = k → b.env gateLength = gs.length →
      C.cw.drop b.cp = gateWord gs[k] ++ ((gs.drop (k + 1)).flatMap gateWord ++ rest) →
      Hs C readCoordinateGate b (120 * (C.cw.length + 2) ^ 2) (fun d =>
        P (k + 1) d ∧ d.env gateIndex = k ∧ d.env gateLength = gs.length ∧
        d.cp = b.cp + (gateWord gs[k]).length) := by
    intro k hk b ⟨hb, hw, ho, hc', hfr⟩ hbi hbn hd
    have hprefix := gate_prefix_arity_bound gs k hk
    have hprice := coordinateSum_le_charge (gs.take k) i
    have bcoord : b.env coordinate=i.val := (hfr _ (by decide)).trans hcoord
    refine Hs.mono (readCoordinateGate_run C gs[k] i _ b hc' bcoord hd hW hL
      (by rw [hb]; omega)) le_rfl ?_
    rintro d ⟨hdtotal, hdcp, hdwq, hdout, hdc, hdfr⟩
    refine ⟨⟨?_, hdwq.trans hw, hdout.trans ho, hdc,
      Fr.trans hfr (Fr.weaken hdfr (by decide))⟩,
      (hdfr _ (by decide)).trans hbi, (hdfr _ (by decide)).trans hbn, hdcp⟩
    rw [hdtotal, hb, coordinateSum_take_succ gs i k hk]
    omega
  have hgs : gs.length ≤ (gs.flatMap gateWord).length :=
    length_le_flatMap gs gateWord (fun g => by have := arity_add_one_le_gateWord g; omega)
  have hwalk := walk (C := C) gs gateWord gateIndex gateLength (by decide)
    readCoordinateGate P (120 * (C.cw.length + 2) ^ 2) rest hp hbody (by omega) a
    ⟨by simp [coordinateSum], rfl, rfl, hc, Fr.refl _ _⟩ hi hn hcw
  refine Hs.mono hwalk le_rfl ?_
  rintro b ⟨⟨hb, hw, ho, hc', hfr⟩, hbi, hbn, hbcp⟩
  exact ⟨by simpa using hb, hbcp, hw, ho, hc', hfr, hbi, hbn⟩


end NearQuarticWires.StageCert.Incidence
