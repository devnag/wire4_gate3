import Proof.Gates.Dispatch.ParamsG

/-!
# The final integer rate-chain fields

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The final `J` and `Lambda` fields of `sec:params`,
paper/paper.tex. -/
def chainFinishProgram : St VV :=
  .seq (assign pJ (add (var pCI) (lit 1)))
    (assign pLB (add (div (mul (sub (var pLW) (lit 1)) (var pA)) (lit 2)) (lit 1)))

/-- The last two integer fields of `sec:params`,
paper/paper.tex, are computed exactly in fixed
arithmetic work, retaining the selected factors and stopping flag. -/
theorem chainFinishProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (i A L : ℕ) (hiv : a.env pCI = i) (hAv : a.env pA = A)
    (hLv : a.env pLW = L) (hW : L * A + i + 8 < 2 ^ C.Wd) :
    Hs C chainFinishProgram a 60 (fun b =>
      b.env pJ = i + 1 ∧ b.env pLB = (L - 1) * A / 2 + 1 ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [pJ, pLB, vJ]) := by
  have hm : (L - 1) * A ≤ L * A := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hd : (L - 1) * A / 2 ≤ L * A := (Nat.div_le_self _ _).trans hm
  unfold chainFinishProgram
  refine Hx.hs (Hs.then (assign_spec pJ (by decide) (by decide)
    (.add (.var pCI) (.lit 1)) a (by aevar) (by aevar) hc (by aeok [hiv]))
    (fun b ⟨hb, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbL : b.env pLW = L := (hbfr _ (by decide) (by decide) (by decide)).trans hLv
  have hbA : b.env pA = A := (hbfr _ (by decide) (by decide) (by decide)).trans hAv
  refine Hs.last (assign_spec pLB (by decide) (by decide)
    (.add (.div (.mul (.sub (.var pLW) (.lit 1)) (.var pA)) (.lit 2)) (.lit 1)) b
    (by aevar) (by aevar) hbc (by aeok [hbL, hbA])) ?_
  rintro d ⟨hdv, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2
  refine ⟨⟨?_, ?_, hdcp.trans hbcp, hdwq.trans hbwq, hdout.trans hbout,
    hdc, FrS.trans (hbfr.toS _ (by decide) (by decide))
      (hdfr.toS _ (by decide) (by decide))⟩, ?_⟩
  · rw [hdfr _ (by decide) (by decide) (by decide), hb]
    simp only [AE.eval, hiv]
  · simpa only [AE.eval, hbL, hbA] using hdv
  · simp only [AE.cost] at hn1 hn2
    omega

end NearQuarticWires.StagePrep
