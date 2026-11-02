import Proof.Quartic.StagePrep.ChainWidths

/-!
# The actual finite rate-chain computation

Paper: `imp:chain`, paper/paper.tex, and
`sec:params`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- The exact rate-chain computation of `sec:params`,
paper/paper.tex, performs the finite stopping
search without writing factors before all public guards pass. -/
def rateChainProgram : St VV := .seq chainInitialProgram (chainP false)

/-- The rate-chain program of `sec:params`, paper/paper.tex, returns the exact stopping result and factor
product on both successful and failed searches. All finite
search work is charged before the final guard. -/
theorem rateChainProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (ell h T S n : ℕ) (hellv : a.env ellZeroReg = ell)
    (hhv : a.env pH = h) (hTv : a.env pT = T)
    (hJv : a.env pJM = Jmax n)
    (hell : 0 < ell) (hh : 0 < h) (hT : 0 < T) (hguard : 64 * T ≤ h)
    (hellS : ell < 2 ^ S) (hhS : h < 2 ^ S) (hTS : T < 2 ^ S)
    (hJS : Jmax n < 2 ^ S) (hSW : 6 * S + 40 ≤ C.Wd) :
    Hs C rateChainProgram a (3021 + chainCost (Jmax n) h) (fun b =>
      b.env pM1 = firstDen (ell : ℚ) h T ∧
      (∃ i, b.env pCI = i ∧ b.env pA = (chainFactors (firstRatio (ell : ℚ) h T) i).prod ∧
        ((b.env pCF = 1 ∧ stopIndex (firstRatio (ell : ℚ) h T) n = some i) ∨
          (b.env pCF = 0 ∧ stopIndex (firstRatio (ell : ℚ) h T) n = none))) ∧
      b.env pA < 2 ^ (5 * S + 22) ∧ b.env pCI ≤ Jmax n - 1 ∧
      firstRatio (ell : ℚ) h T = (b.env pXN : ℚ) / b.env pXD ∧
      0 < b.env pXN ∧ b.env pXN ≤ b.env pXD ∧
      b.env pXD ≤ (h + 32) * b.env pXN ∧ b.env pXD < 2 ^ (5 * S + 22) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b (pX1 :: pX2 :: barT ++ chT)) := by
  unfold rateChainProgram
  refine Hx.hs (Hs.then (chainInitialProgram_spec C a hc ell h T S hellv hhv hTv
    hell hh hT hguard hellS hhS hTS (by omega))
    (fun b ⟨hbM, hbx, hbN0, hbD0, hbND, hbDle, hbcap,
      hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbJ : b.env pJM = Jmax n := (hbfr _ (by decide) (by decide)).trans hJv
  have hwidth := (chain_width_bounds S (b.env pXD) h (Jmax n) 0 C.Wd
    hbcap hhS hJS (by positivity) hSW).1
  refine Hs.last (chainP_spec b hbc false (firstRatio (ell : ℚ) h T) n
    (b.env pXN) (b.env pXD) h rfl rfl hbJ hbx hbN0 hbND hbDle hwidth (by omega)) ?_
  rintro d ⟨⟨i, hdi, hdA, hdout, hdstop⟩, hdAD, hdiJ, hdcp, hdwq, hdc, hdfr⟩ n2 hn2
  have hdXN : d.env pXN = b.env pXN := hdfr _ (by decide) (by decide)
  have hdXD : d.env pXD = b.env pXD := hdfr _ (by decide) (by decide)
  refine ⟨⟨?_, ⟨i, hdi, hdA, hdstop⟩, hdAD.trans_lt hbcap, hdiJ,
    ?_, ?_, ?_, ?_, ?_, hdcp.trans hbcp, hdwq.trans hbwq, ?_, hdc,
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr (by decide))⟩, by omega⟩
  · rw [hdfr _ (by decide) (by decide), hbM]
  · rw [hdXN, hdXD]
    exact hbx
  · rw [hdXN]
    exact hbN0
  · rw [hdXN, hdXD]
    exact hbND
  · rw [hdXN, hdXD]
    exact hbDle
  · rw [hdXD]
    exact hbcap
  · simpa only [Bool.false_eq_true, ↓reduceIte, List.append_nil, hbout] using hdout

end NearQuarticWires.StagePrep
