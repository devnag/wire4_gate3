import Proof.Gates.Dispatch.ParamsD

/-!
# The exact prime windows

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open NearCubicGates

/-- The prime census and both window calculations of
`sec:params`, paper/paper.tex. -/
def primeWindowsProgram : St VV := .seq pPrimes (.seq pPair pLw)

/-- The prime census of `sec:params`, paper/paper.tex, computes all three literal windows by actual finite
integer loops without inspecting the counting witness. -/
theorem primeWindowsProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (P : ℕ) (pair : Bool) (hPv : a.env pP = P)
    (hTag : a.env vTAG = 1 ↔ pair = true)
    (hW : 2 * (P + 1) * (P + 1) + 8 < 2 ^ C.Wd)
    (hD : 2 * (ScalarWindow.window (dyadicPrimes P) *
      (ScalarWindow.window (dyadicPrimes P) * ScalarWindow.window (dyadicPrimes P))) +
      2 * ScalarWindow.window (dyadicPrimes P) + 8 < 2 ^ C.Wd) :
    Hs C primeWindowsProgram a
      (primesCost P + pairCost (ScalarWindow.window (dyadicPrimes P)) + 10)
      (fun b => b.env pNP = (dyadicPrimes P).card ∧
        b.env pWIN = ScalarWindow.window (dyadicPrimes P) ∧
        b.env pL2 = pairSide (ScalarWindow.window (dyadicPrimes P)) ∧
        b.env pLW = windowInUse pair (pairSide (ScalarWindow.window (dyadicPrimes P)))
          (ScalarWindow.window (dyadicPrimes P)) ∧ b.env pP = P ∧
        b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
        FrS a b (prT ++ pairT ++ [pLW, vJ])) := by
  unfold primeWindowsProgram
  refine Hx.hs (Hs.then (pPrimes_spec a hc P hPv hW)
    (fun b ⟨hbN, hbD, hbP, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  refine Hs.then (pPair_spec b hbc _ hbD hD)
    (fun d ⟨hdL, hdD, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdTag : d.env vTAG = 1 ↔ pair = true := by
    rw [hdfr _ (by decide) (by decide), hbfr _ (by decide) (by decide)]
    exact hTag
  refine Hs.last (pLw_spec d hdc pair _ _ hdTag hdL hdD) ?_
  rintro e ⟨heL, hecp, hewq, heout, hec, hefr⟩ n3 hn3
  refine ⟨⟨?_, ?_, ?_, heL, ?_, hecp.trans (hdcp.trans hbcp),
    hewq.trans (hdwq.trans hbwq), heout.trans (hdout.trans hbout), hec,
    FrS.trans (FrS.weaken hbfr (by decide))
      (FrS.trans (FrS.weaken hdfr (by decide))
        (hefr.toS _ (by decide) (by decide)))⟩, ?_⟩
  · rw [hefr _ (by decide) (by decide) (by decide),
      hdfr _ (by decide) (by decide), hbN]
  · rw [hefr _ (by decide) (by decide) (by decide), hdD]
  · rw [hefr _ (by decide) (by decide) (by decide), hdL]
  · rw [hefr _ (by decide) (by decide) (by decide),
      hdfr _ (by decide) (by decide), hbP]
  · omega

end NearQuarticWires.StagePrep
