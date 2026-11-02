import Proof.Quartic.StagePrep.CensusGateBounds

/-!
# The physical occurrence-list census

Paper: `def:class`, paper/paper.tex, and
`prop:time`. Every occurrence is read separately.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces

/-- The occurrence index of `def:class`, paper/paper.tex. -/
def gateIndex : Fin VV := ⟨65, by decide⟩

/-- The occurrence count of `def:class`, paper/paper.tex. -/
def gateLength : Fin VV := ⟨66, by decide⟩

/-- The occurrence loop of `def:class`, paper/paper.tex. -/
def countGates : St VV :=
  .loop (.lt gateIndex gateLength) (.seq countGate (.op (.inc gateIndex)))

/-- The literal gate-list loop of `def:class`, paper/paper.tex, sums the actual wire count and preserves all other
parsed call fields. -/
theorem countGates_spec (C : Ctx) {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hi : a.env gateIndex = 0) (hn : a.env gateLength = gs.length)
    (hcw : C.cw.drop a.cp = gs.flatMap gateWord ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + (gs.flatMap gateWord).length + 2 < 2 ^ C.Wd) :
    Hs C countGates a (gs.length * (120 * (C.cw.length + 2) ^ 2 + 4) + 2)
      (fun b => b.env censusTotal = a.env censusTotal + gateChargeSum gs ∧
        b.cp = a.cp + (gs.flatMap gateWord).length ∧
        b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
        Fr a b (gateIndex :: gateCensusT) ∧
        b.env gateIndex = gs.length ∧ b.env gateLength = gs.length) := by
  let T := gateIndex :: gateCensusT
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env censusTotal = a.env censusTotal + gateChargeSum (gs.take k) ∧
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
      Hs C countGate b (120 * (C.cw.length + 2) ^ 2) (fun d =>
        P (k + 1) d ∧ d.env gateIndex = k ∧ d.env gateLength = gs.length ∧
        d.cp = b.cp + (gateWord gs[k]).length) := by
    intro k hk b ⟨hb, hw, ho, hc', hfr⟩ hbi hbn hd
    have hprefix := gate_prefix_arity_bound gs k hk
    refine Hs.mono (countGate_spec C gs[k] _ b hc' hd hW hL
      (by rw [hb]; omega)) le_rfl ?_
    rintro d ⟨hdtotal, hdcp, hdwq, hdout, hdc, hdfr⟩
    refine ⟨⟨?_, hdwq.trans hw, hdout.trans ho, hdc,
      Fr.trans hfr (Fr.weaken hdfr (by decide))⟩,
      (hdfr _ (by decide)).trans hbi, (hdfr _ (by decide)).trans hbn, hdcp⟩
    rw [hdtotal, hb, gateChargeSum_take_succ gs k hk]
    omega
  have hgs : gs.length ≤ (gs.flatMap gateWord).length :=
    length_le_flatMap gs gateWord (fun g => by have := arity_add_one_le_gateWord g; omega)
  have hwalk := walk (C := C) gs gateWord gateIndex gateLength (by decide)
    countGate P (120 * (C.cw.length + 2) ^ 2) rest hp hbody (by omega) a
    ⟨by simp [gateChargeSum], rfl, rfl, hc, Fr.refl _ _⟩ hi hn hcw
  refine Hs.mono hwalk le_rfl ?_
  rintro b ⟨⟨hb, hw, ho, hc', hfr⟩, hbi, hbn, hbcp⟩
  exact ⟨by simpa using hb, hbcp, hw, ho, hc', hfr, hbi, hbn⟩

end NearQuarticWires.StagePrep
