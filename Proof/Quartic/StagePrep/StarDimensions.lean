import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# The star-block side lengths

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`. Powers of two are
constructed by shifts, not by unary output.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The exact `b,k,N` rules of `sec:params`, paper/paper.tex. -/
def starDimensionsProgram : St VV :=
  .seq (.op (.copy P2E sReg)) (.seq pow2v
    (.seq (assign bReg (sub (var P2X) (lit 1)))
      (.seq (assign pK (mul (var rReg) (var sReg)))
        (.seq (assign P2E (div (var pK) (lit 2)))
          (.seq pow2v (assign nSideReg (var P2X)))))))

/-- The registers changed by `sec:params`, paper/paper.tex, while constructing the dimensions. -/
def starDimensionsT : List (Fin VV) := [P2E, P2X, P2I, bReg, pK, nSideReg, vJ]

/-- The dimension program of `sec:params`, paper/paper.tex, constructs the exact binary values with a
polynomial number of shifts and arithmetic operations. -/
theorem starDimensionsProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n r s : ℕ) (hr : a.env rReg = r) (hs : a.env sReg = s)
    (hrle : r ≤ n) (hsle : s ≤ n + 1)
    (hW : n * (n + 1) + n + 32 ≤ C.Wd) :
    Hs C starDimensionsProgram a (10 * n * (n + 1) + 10 * n + 200) (fun b =>
      b.env bReg = 2 ^ s - 1 ∧ b.env pK = r * s ∧
      b.env nSideReg = 2 ^ (r * s / 2) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b starDimensionsT) := by
  have hrs : r * s ≤ n * (n + 1) := Nat.mul_le_mul hrle hsle
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hsW : s < C.Wd := by omega
  have hkW : r * s / 2 < C.Wd := by omega
  have hksmall : r * s < 2 ^ C.Wd := by omega
  have hfour : 4 ≤ 2 ^ C.Wd := by omega
  unfold starDimensionsProgram
  refine Hx.hs (Hs.then (hs_copy C P2E sReg a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set P2E (a.env sReg)) := hc.set _ _ (by decide)
  refine Hs.then (pow2v_spec _ hc0 s (by rw [DS.set_env_self, hs]) hsW)
    (fun b ⟨hbx, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_)
  refine Hs.then (assign_spec bReg (by decide) (by decide)
    (.sub (.var P2X) (.lit 1)) b (by aevar) (by aevar) hbc (by aeok []))
    (fun d ⟨hdb, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hdr : d.env rReg = r := by
    rw [hdfr _ (by decide) (by decide) (by decide), hbfr _ (by decide),
      DS.set_env_ne _ _ (by decide), hr]
  have hds : d.env sReg = s := by
    rw [hdfr _ (by decide) (by decide) (by decide), hbfr _ (by decide),
      DS.set_env_ne _ _ (by decide), hs]
  have hdb' : d.env bReg = 2 ^ s - 1 := by simpa only [AE.eval, hbx] using hdb
  refine Hs.then (assign_spec pK (by decide) (by decide)
    (.mul (.var rReg) (.var sReg)) d (by aevar) (by aevar) hdc
    (by aeok [hdr, hds]))
    (fun e ⟨hek, hefr, hecp, hewq, heout, hec⟩ n3 hn3 => ?_)
  have hek' : e.env pK = r * s := by simpa only [AE.eval, hdr, hds] using hek
  refine Hs.then (assign_spec P2E (by decide) (by decide)
    (.div (.var pK) (.lit 2)) e (by aevar) (by aevar) hec (by aeok []))
    (fun f ⟨hfe, hffr, hfcp, hfwq, hfout, hfc⟩ n4 hn4 => ?_)
  have hfe' : f.env P2E = r * s / 2 := by simpa only [AE.eval, hek'] using hfe
  refine Hs.then (pow2v_spec f hfc _ hfe' hkW)
    (fun g ⟨hgx, hgcp, hgwq, hgout, hgc, hgfr⟩ n5 hn5 => ?_)
  refine Hs.last (assign_spec nSideReg (by decide) (by decide) (.var P2X) g
    (by aevar) (by aevar) hgc (by trivial))
    (fun h ⟨hhn, hhfr, hhcp, hhwq, hhout, hhc⟩ n6 hn6 => ?_)
  have hfr : FrS a h starDimensionsT :=
    FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (FrS.weaken hbfr.toS (by decide))
        (FrS.trans (hdfr.toS _ (by decide) (by decide))
          (FrS.trans (hefr.toS _ (by decide) (by decide))
            (FrS.trans (hffr.toS _ (by decide) (by decide))
              (FrS.trans (FrS.weaken hgfr.toS (by decide))
                (hhfr.toS _ (by decide) (by decide)))))))
  refine ⟨⟨?_, ?_, ?_, hhcp.trans (hgcp.trans (hfcp.trans (hecp.trans (hdcp.trans hbcp)))),
    hhwq.trans (hgwq.trans (hfwq.trans (hewq.trans (hdwq.trans hbwq)))),
    hhout.trans (hgout.trans (hfout.trans (heout.trans (hdout.trans hbout)))), hhc, hfr⟩, ?_⟩
  · rw [hhfr _ (by decide) (by decide) (by decide), hgfr _ (by decide),
      hffr _ (by decide) (by decide) (by decide), hefr _ (by decide) (by decide) (by decide), hdb']
  · rw [hhfr _ (by decide) (by decide) (by decide), hgfr _ (by decide),
      hffr _ (by decide) (by decide) (by decide), hek']
  · simpa only [AE.eval, hgx] using hhn
  · simp only [AE.cost] at hn2 hn3 hn4 hn6
    have hn5' : n5 ≤ 5 * (r * s / 2) + 6 := hn5
    rw [show 10 * n * (n + 1) = 10 * (n * (n + 1)) by ring]
    omega

end NearQuarticWires.StagePrep
