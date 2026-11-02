import Proof.Quartic.StagePrep.CensusArithmetic

/-!
# The physical census of a gate's input weights

Paper: `def:class`, paper/paper.tex, and the
polynomial preparation cost of `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces

/-- The input-weight index of `def:class`, paper/paper.tex. -/
def weightIndex : Fin VV := ⟨63, by decide⟩

/-- The encoded input-weight count of `def:class`,
paper/paper.tex. -/
def weightLength : Fin VV := ⟨64, by decide⟩

/-- The input-weight loop of `def:class`, paper/paper.tex. -/
def countWeights : St VV :=
  .loop (.lt weightIndex weightLength) (.seq countWeight (.op (.inc weightIndex)))

/-- The input-weight census in `def:class`, paper/paper.tex, follows the encoded list once and counts precisely its
nonzero entries. -/
theorem countWeights_spec (C : Ctx) (ws : List ℤ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (hi : a.env weightIndex = 0)
    (hn : a.env weightLength = ws.length)
    (hcw : C.cw.drop a.cp = ws.flatMap intWord ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + ws.length + 1 < 2 ^ C.Wd) :
    Hs C countWeights a (ws.length * (60 * C.cw.length + 77) + 2) (fun b =>
      b.env censusTotal = a.env censusTotal + wireSum ws ∧
      b.cp = a.cp + (ws.flatMap intWord).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b (weightIndex :: censusTotal :: readIntT) ∧
      b.env weightIndex = ws.length ∧ b.env weightLength = ws.length) := by
  let T := weightIndex :: censusTotal :: readIntT
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env censusTotal = a.env censusTotal + wireSum (ws.take k) ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b T
  have hp : ∀ k b v, P k b → P k (b.set weightIndex v) := by
    rintro k b v ⟨hb, hw, ho, hc', hfr⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb, hw, ho,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.pos⟩,
      Fr.trans hfr (Fr.set _ _ (by decide))⟩
  have hbody : ∀ k (hk : k < ws.length) (b : DS VV), P k b →
      b.env weightIndex = k → b.env weightLength = ws.length →
      C.cw.drop b.cp = intWord ws[k] ++ ((ws.drop (k + 1)).flatMap intWord ++ rest) →
      Hs C countWeight b (60 * C.cw.length + 73) (fun d =>
        P (k + 1) d ∧ d.env weightIndex = k ∧ d.env weightLength = ws.length ∧
        d.cp = b.cp + (intWord ws[k]).length) := by
    intro k hk b ⟨hb, hw, ho, hc', hfr⟩ hbi hbn hd
    have htake := (wireSum_le_length (ws.take k)).trans
      (show (ws.take k).length ≤ ws.length by simp)
    have hentry := len_le_of_drop hd
    refine Hs.mono (countWeight_spec C b hc' ws[k] _ hd hW hL (by rw [hb]; omega))
      (by omega) ?_
    rintro d ⟨hdtotal, hdcp, hdwq, hdout, hdc, hdfr⟩
    refine ⟨⟨?_, hdwq.trans hw, hdout.trans ho, hdc,
      Fr.trans hfr (Fr.weaken hdfr (by decide))⟩,
      (hdfr _ (by decide)).trans hbi, (hdfr _ (by decide)).trans hbn, hdcp⟩
    rw [hdtotal, hb, wireSum_take_succ ws k hk]
    omega
  have hwalk := walk (C := C) ws intWord weightIndex weightLength (by decide)
    countWeight P (60 * C.cw.length + 73) rest hp hbody (by omega) a
    ⟨by simp [wireSum], rfl, rfl, hc, Fr.refl _ _⟩ hi hn hcw
  refine Hs.mono hwalk le_rfl ?_
  rintro b ⟨⟨hb, hw, ho, hc', hfr⟩, hbi, hbn, hbcp⟩
  exact ⟨by simpa using hb, hbcp, hw, ho, hc', hfr, hbi, hbn⟩

end NearQuarticWires.StagePrep
