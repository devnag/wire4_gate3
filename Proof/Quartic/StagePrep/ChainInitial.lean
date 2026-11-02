import Proof.Quartic.StagePrep.ChainHeight
import Proof.Gates.Dispatch.ParamsF

/-!
# The initial exact rational rate

Paper: `imp:chain`, paper/paper.tex, and
`sec:params`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- The integer initial scale of `sec:params`, paper/paper.tex, is supplied directly to the exact rational
maximum and ceiling calculation. -/
def chainInitialProgram : St VV :=
  .seq (.op (.copy pX1 ellZeroReg))
    (.seq (assign pX2 (.lit 1)) pBar)

/-- The exact initial ratio for `imp:chain`, `lem:selector`, paper/paper.tex, has a positive integer numerator and denominator
and satisfies the invariant required by every later chain step. -/
theorem chainInitialProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (ell h T S : ℕ) (hellv : a.env ellZeroReg = ell)
    (hhv : a.env pH = h) (hTv : a.env pT = T)
    (hell : 0 < ell) (hh : 0 < h) (hT : 0 < T) (hguard : 64 * T ≤ h)
    (hellS : ell < 2 ^ S) (hhS : h < 2 ^ S) (hTS : T < 2 ^ S)
    (hSW : 5 * S + 30 ≤ C.Wd) :
    Hs C chainInitialProgram a 3020 (fun b =>
      b.env pM1 = firstDen (ell : ℚ) h T ∧
      firstRatio (ell : ℚ) h T = (b.env pXN : ℚ) / b.env pXD ∧
      0 < b.env pXN ∧ 0 < b.env pXD ∧ b.env pXN ≤ b.env pXD ∧
      b.env pXD ≤ (h + 32) * b.env pXN ∧ b.env pXD < 2 ^ (5 * S + 22) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b (pX1 :: pX2 :: barT)) := by
  have hS : 0 < S := by
    by_contra hs
    have : S = 0 := by omega
    simp [this] at hellS
    omega
  have h1S : 1 < 2 ^ S := (Nat.one_lt_two_pow_iff).2 (by omega)
  have h1W : 1 < 2 ^ C.Wd := lt_pow_mono h1S (by omega)
  unfold chainInitialProgram
  refine Hx.hs (Hs.then (hs_copy C pX1 ellZeroReg a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  refine Hs.then (assign_spec pX2 (by decide) (by decide) (.lit 1)
    (a.set pX1 (a.env ellZeroReg)) (by aevar) (by aevar)
    (hc.set _ _ (by decide)) (by aeok []))
    (fun d ⟨hd, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hd1 : d.env pX1 = ell := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_self, hellv]
  have hd2 : d.env pX2 = 1 := hd
  have hdh : d.env pH = h := by
    rw [hdfr _ (by decide) (by decide) (by decide),
      DS.set_env_ne _ _ (by decide), hhv]
  have hdT : d.env pT = T := by
    rw [hdfr _ (by decide) (by decide) (by decide),
      DS.set_env_ne _ _ (by decide), hTv]
  refine Hs.last (pBar_spec d hdc ell 1 h T S hd1 hd2 hdh hdT hell
    (by omega) hh hT hellS h1S hhS hTS hSW) ?_
  rintro e ⟨hebar, heM, heXN, heXD, hex, heN0, heD0, heDle, he4, hecap,
    hecp, hewq, heout, hec, hefr⟩ n3 hn3
  have heND : e.env pXN ≤ e.env pXD := by
    rw [heXN]
    exact (Nat.mul_le_mul_right _ (show 8 * T ≤ 4 * h by omega)).trans he4
  refine ⟨⟨?_, ?_, heN0, heD0, heND, heDle, hecap,
    hecp.trans hdcp, hewq.trans hdwq, heout.trans hdout, hec, ?_⟩, ?_⟩
  · simpa only [Nat.cast_one, div_one] using heM
  · simpa only [Nat.cast_one, div_one] using hex
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.weaken hefr (by decide)))
  · simp only [AE.cost] at hn2
    omega

end NearQuarticWires.StagePrep
