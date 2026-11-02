import Proof.Quartic.StagePrep.PrefixPhysical
import Proof.Gates.Dispatch.ParamsG

/-!
# The exact public witness-prefix length

Paper: witness (W1)–(W3), paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The finite prefix length from `sec:algorithm`, paper/paper.tex is computed before any witness bit is read. The
limit register is filled only after expression evaluation. -/
def prefixLengthProgram : St VV :=
  .seq (assign pX1 (add (var pK)
    (mul (add (var pJ) (lit 1)) (add (var vG1) (var vG2)))))
    (.op (.copy prefixLimit pX1))

/-- The exact integer prefix-length computation in
`sec:algorithm`, paper/paper.tex preserves every source field
and does not inspect the witness suffix. -/
theorem prefixLengthProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (k J G1 G2 : ℕ) (hkv : a.env pK = k) (hJv : a.env pJ = J)
    (hG1v : a.env vG1 = G1) (hG2v : a.env vG2 = G2)
    (hW : k + (J + 1) * (G1 + G2) + J + G1 + G2 + 16 < 2 ^ C.Wd) :
    Hs C prefixLengthProgram a 60 (fun b =>
      b.env prefixLimit = k + (J + 1) * (G1 + G2) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [pX1, vJ]) := by
  unfold prefixLengthProgram
  refine Hx.hs (Hs.then (assign_spec pX1 (by decide) (by decide)
    (.add (.var pK) (.mul (.add (.var pJ) (.lit 1)) (.add (.var vG1) (.var vG2)))) a
    (by aevar) (by aevar) hc (by aeok [hkv, hJv, hG1v, hG2v]))
    (fun b ⟨hb, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  refine Hs.last (hs_copy C prefixLimit pX1 b (by decide)) ?_
  rintro d rfl n2 hn2
  refine ⟨⟨?_, hbcp, hbwq, hbout, hbc.set _ _ (by decide), ?_⟩, ?_⟩
  · rw [DS.set_env_self, hb]
    simp only [AE.eval, hkv, hJv, hG1v, hG2v]
  · intro v hv hnot
    rw [DS.set_env_ne _ _ (by intro heq; subst heq; exact (by decide : ¬ prefixLimit.val < 200) hv)]
    exact hbfr v hv (fun heq => hnot (by simp [heq])) (fun heq => hnot (by simp [heq]))
  · simp only [AE.cost] at hn1
    omega

end NearQuarticWires.StagePrep
