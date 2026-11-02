import Proof.Quartic.StagePrep.ClosedOutput
import Proof.Quartic.StagePrep.ClosedMath

/-!
# The exact zero-wire preparation exit

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces

/-- A zero-wire call in `sec:params`, paper/paper.tex, is answered by the actual constant-call program with
exactly the required preparation word for every witness. -/
theorem closedZeroOutput_prepWord_spec (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (w : List Bool) (ha : Transfer.Admitted4 B1 B2 c) (hz : Transfer.callWires c = 0)
    (a : DS VV) (hc : Cst a) (hpo : ParseOut c a)
    (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C closedZeroOutput a
      (oddCostT C.cw.length c.parity.length C.Wd + 2 * closedZeroWordLen + 50)
      (fun b => b.out = a.out ++ Program.prepWord B1 B2 c w ∧
        Cst b ∧ b.wq = a.wq ∧ FrS a b zoT) := by
  have hall : ∀ i ∈ c.parity, i < c.n := ha.2.2.2.2.2.2.2.1
  rw [prepWord_of_zero c w ha hz, closedValue_eq_zval c hall]
  exact closedZeroOutput_spec C B1 B2 c (Program.admitted_of_admitted4 ha) a hc hpo hcw hW hL

end NearQuarticWires.StagePrep
