import Proof.Gates.Dispatch.ParamsMath
import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# Exact ceilings of positive-denominator rationals

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The natural numerator for `sec:params`, paper/paper.tex. -/
def rationalNumReg : Fin VV := ⟨92, by decide⟩
/-- The positive denominator for `sec:params`, paper/paper.tex. -/
def rationalDenReg : Fin VV := ⟨93, by decide⟩
/-- The integer ceiling for `sec:params`, paper/paper.tex. -/
def rationalCeilReg : Fin VV := ⟨94, by decide⟩

/-- The integer quotient computation for rational ceilings in
`sec:params`, paper/paper.tex. -/
def rationalCeilProgram : St VV := assign rationalCeilReg
  (div (sub (add (var rationalNumReg) (var rationalDenReg)) (lit 1))
    (var rationalDenReg))

/-- The rational-ceiling computation of `sec:params`,
paper/paper.tex, is exactly integer arithmetic,
including a zero numerator. -/
theorem rationalCeilProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (A B : ℕ) (hA : a.env rationalNumReg = A)
    (hB : a.env rationalDenReg = B) (hBpos : 0 < B)
    (hW : A + 2 * B + 4 < 2 ^ C.Wd) :
    Hs C rationalCeilProgram a 21 (fun b =>
      b.env rationalCeilReg = ⌈(A : ℚ) / B⌉₊ ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [rationalCeilReg, vJ]) := by
  unfold rationalCeilProgram
  refine Hs.mono (assign_spec rationalCeilReg (by decide) (by decide)
    (.div (.sub (.add (.var rationalNumReg) (.var rationalDenReg)) (.lit 1))
      (.var rationalDenReg)) a (by aevar) (by aevar) hc (by aeok [hA, hB]))
    le_rfl ?_
  rintro b ⟨hb, hfr, hcp, hwq, hout, hbc⟩
  refine ⟨?_, hcp, hwq, hout, hbc, hfr.toS _ (by decide) (by decide)⟩
  rw [ceil_div_nat A B hBpos]
  simpa only [AE.eval, hA, hB] using hb

end NearQuarticWires.StagePrep
