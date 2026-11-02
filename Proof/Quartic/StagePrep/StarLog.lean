import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# The exact star-block logarithm

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The star-block logarithm of `sec:params`, paper/paper.tex, uses integer division and the floor logarithm. -/
def starLogProgram : St VV :=
  .seq (assign LGX (add (div (var vN) (var rReg)) (lit 1)))
    (.seq log2v (assign sReg (var LGR)))

/-- The floor-logarithm computation of `sec:params`,
paper/paper.tex, exactly matches the canonical
parameter rule and preserves the other public fields. -/
theorem starLogProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n r : ℕ) (hn : a.env vN = n) (hr : a.env rReg = r)
    (hrpos : 0 < r) (hrle : r ≤ n) (hW : 2 * n + 4 < 2 ^ C.Wd) :
    Hs C starLogProgram a (5 * n + 50) (fun b =>
      b.env sReg = Nat.log 2 (n / r + 1) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [LGX, LGR, LGT, sReg, vJ]) := by
  have hdiv : n / r ≤ n := Nat.div_le_self _ _
  have hlog : Nat.log 2 (n / r + 1) ≤ n + 1 :=
    (Nat.log_le_self _ _).trans (by omega)
  unfold starLogProgram
  refine Hx.hs (Hs.then (assign_spec LGX (by decide) (by decide)
    (.add (.div (.var vN) (.var rReg)) (.lit 1)) a (by aevar) (by aevar) hc
    (by aeok [hn, hr]))
    (fun b ⟨hbx, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbx' : b.env LGX = n / r + 1 := by simpa only [AE.eval, hn, hr] using hbx
  refine Hs.then (log2v_spec b hbc _ hbx' (by omega))
    (fun d ⟨hdl, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  refine Hs.last (assign_spec sReg (by decide) (by decide) (.var LGR) d
    (by aevar) (by aevar) hdc (by trivial))
    (fun e ⟨hes, hefr, hecp, hewq, heout, hec⟩ n3 hn3 => ?_)
  refine ⟨⟨?_, hecp.trans (hdcp.trans hbcp),
    hewq.trans (hdwq.trans hbwq), heout.trans (hdout.trans hbout), hec, ?_⟩, ?_⟩
  · simpa only [AE.eval, hdl] using hes
  · exact FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (FrS.weaken hdfr.toS (by decide)) (hefr.toS _ (by decide) (by decide)))
  · simp only [AE.cost] at hn1 hn3
    omega

end NearQuarticWires.StagePrep
