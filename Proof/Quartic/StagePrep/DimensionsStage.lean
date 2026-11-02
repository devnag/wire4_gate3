import Proof.Quartic.StagePrep.StarLog
import Proof.Quartic.StagePrep.StarDimensions

/-!
# The complete star-dimension computation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The consecutive star logarithm and dimension operations of
`sec:params`, paper/paper.tex. -/
def dimensionsStage : St VV := .seq starLogProgram starDimensionsProgram

/-- The exact star parameters of `sec:params`,
paper/paper.tex, are all retained after the
complete public dimension computation. -/
theorem dimensionsStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n r : ℕ) (hn : a.env vN = n) (hr : a.env rReg = r)
    (hrpos : 0 < r) (hrle : r ≤ n)
    (hW : n * (n + 1) + 2 * n + 32 ≤ C.Wd) :
    Hs C dimensionsStage a (10 * n * (n + 1) + 15 * n + 251) (fun b =>
      b.env sReg = Nat.log 2 (n / r + 1) ∧
      b.env bReg = 2 ^ Nat.log 2 (n / r + 1) - 1 ∧
      b.env pK = r * Nat.log 2 (n / r + 1) ∧
      b.env nSideReg = 2 ^ (r * Nat.log 2 (n / r + 1) / 2) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b ([LGX, LGR, LGT, sReg, vJ] ++ starDimensionsT)) := by
  have hWpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hs : Nat.log 2 (n / r + 1) ≤ n + 1 :=
    (Nat.log_le_self _ _).trans (by have := Nat.div_le_self n r; omega)
  unfold dimensionsStage
  refine Hx.hs (Hs.then (starLogProgram_spec C a hc n r hn hr hrpos hrle (by omega))
    (fun b ⟨hbs, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbr : b.env rReg = r := (hbfr _ (by decide) (by decide)).trans hr
  refine Hs.last (starDimensionsProgram_spec C b hbc n r _ hbr hbs hrle hs (by omega)) ?_
  rintro d ⟨hdb, hdk, hdN, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2
  refine ⟨⟨?_, hdb, hdk, hdN, hdcp.trans hbcp, hdwq.trans hbwq,
    hdout.trans hbout, hdc, FrS.trans (FrS.weaken hbfr (by decide))
      (FrS.weaken hdfr (by decide))⟩, by omega⟩
  exact (hdfr _ (by decide) (by decide)).trans hbs

end NearQuarticWires.StagePrep
