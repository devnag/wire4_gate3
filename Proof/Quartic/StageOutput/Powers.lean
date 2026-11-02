import Proof.Quartic.StageOutput.Numerators
import Proof.Gates.Dispatch.Arith2

/-!
# The two binary powers used in Step 5

Paper: `sec:algorithm`, paper/paper.tex. The exact endpoint
numerators use `2^k` and `2^n`; their binary construction costs linearly many
shifts in the exponents, within the allocated arithmetic width.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def powersProgram : St VV :=
  .seq (.op (.copy P2E 20)) (.seq pow2v (.seq (.op (.copy powerN P2X))
    (.seq (.op (.copy P2E 21)) (.seq pow2v (.op (.copy powerK P2X))))))

def powersScratch : List (Fin VV) := [P2E, P2X, P2I, powerN, powerK]

theorem powersProgram_spec {C : Ctx} (a : DS VV) (hc : Cst a) (n k : ℕ)
    (hn : a.env 20 = n) (hk : a.env 21 = k) (hnW : n < C.Wd) (hkW : k < C.Wd) :
    Hs C powersProgram a (5 * n + 5 * k + 21) (fun b =>
      b.env powerN = 2 ^ n ∧ b.env powerK = 2 ^ k ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b powersScratch) := by
  refine Hx.hs (Hs.then (hs_copy C P2E 20 a (by decide)) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (pow2v_spec _ (hc.set _ _ (by decide)) n (by simp [hn]) hnW)
    (fun b ⟨bx, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_)
  refine Hs.then (hs_copy C powerN P2X b (by decide)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  refine Hs.then (hs_copy C P2E 21 _ (by decide)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  have bK : b.env 21 = k := by
    rw [bf 21 (by decide), DS.set_env_ne _ _ (by decide), hk]
  have cc : Cst ((b.set powerN (b.env P2X)).set P2E ((b.set powerN (b.env P2X)).env 21)) :=
    (bc.set _ _ (by decide)).set _ _ (by decide)
  refine Hs.then (pow2v_spec _ cc k (by
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), bK]) hkW)
    (fun d ⟨dx, dp, dw, dout, dc, df⟩ n4 hn4 => ?_)
  refine Hs.last (hs_copy C powerK P2X d (by decide)) ?_
  rintro e rfl n5 hn5
  refine ⟨⟨?_, by simp [dx], by rw [DS.set_cp, dp]; exact bp,
    by rw [DS.set_wq, dw]; exact bw, by rw [DS.set_out, dout]; exact bo,
    dc.set _ _ (by decide), ?_⟩, by omega⟩
  · rw [DS.set_env_ne _ _ (by decide), df powerN (by decide),
      DS.set_env_ne _ _ (by decide), DS.set_env_self, bx]
  · exact Fr.trans (Fr.set a (x := P2E) _ (by decide))
      (Fr.trans (bf.weaken (by decide))
        (Fr.trans (Fr.set b (x := powerN) _ (by decide))
          (Fr.trans (Fr.set _ (x := P2E) _ (by decide))
            (Fr.trans (df.weaken (by decide)) (Fr.set d (x := powerK) _ (by decide))))))

end NearQuarticWires.StageOutput
