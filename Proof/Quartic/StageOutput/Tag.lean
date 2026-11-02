import Proof.Quartic.StageOutput.Codec
import Proof.Gates.Dispatch.Print

/-!
# Reading the output branch tag

Paper: `sec:params`, paper/paper.tex, and
`sec:algorithm`. The tag distinguishes an encoded answer
from the scalar inputs of Step 5, before either branch consumes its payload.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def initializeTag : St VV := .seq constants rdc

theorem initializeTag_spec {C : Ctx} (tag : Bool) (payload : List Bool)
    (hin : C.cw = tag :: payload) (hW : 2 ≤ C.Wd) (hL : C.cw.length < 2 ^ C.Wd) :
    Hs C initializeTag a0 9 (fun b => Cst b ∧ Valid C b ∧
      b.env t0 = tag.toNat ∧ b.cp = 1 ∧ b.wq = 0 ∧ b.out = []) := by
  have hv : Valid C (a0 (V := VV)) := ⟨by intro x; simp [a0], by simp [a0], by simp [a0]⟩
  refine Hs.seq (t2 := 3) (Hs.addValid (by omega) hv (constants_spec hW))
    (fun a ⟨⟨hc, hp, hw, ho⟩, hav⟩ => ?_)
  refine Hs.mono (Hs.addValid (by omega) hav
    (rdc_spec a hc.pos (by rw [hp, hin]; simp) hL)) le_rfl ?_
  rintro b ⟨⟨ht, hpos, hcp, hwq, hout, hfr⟩, hbv⟩
  refine ⟨Cst.of_fr hc hfr (by decide) (by rw [hpos, hcp]), hbv, ?_, by omega,
    by rw [hwq, hw], by rw [hout, ho]⟩
  rw [ht, hin, hp]
  rfl

end NearQuarticWires.StageOutput
