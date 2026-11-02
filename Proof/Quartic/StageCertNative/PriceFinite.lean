import Proof.Quartic.StageCertNative.PriceBasic
import Proof.Quartic.StageFormulaMetadata.FiniteMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: measured
finite-source allocation and ordinary compilation have a quadratic
word factor and a linear dependence on the actual source steps. -/
theorem finiteBudget_product_bound (K : Callee) (V M : ℕ)
    (bits : List Bool) (steps : ℕ) :
    StageFormulaMetadata.finiteBudget K V M bits steps≤
      (100000000*(V+M+TSK K+10))*(bits.length+1)^2*(steps+1) := by
  unfold StageFormulaMetadata.finiteBudget StageFormulaMetadata.finiteInitializeCost
    StageFormulaMetadata.finiteSetupACost StageFormulaMetadata.finiteWidth costB costC
  ring_nf
  omega

/-- `prop:time`, paper/paper.tex: the exact
finite compiler preserves the explicit occurrence exponent of a
source with an original-arity polynomial input. -/
theorem JobPrice.finite {B1 B2 : ℕ} {input : TermJob B1 B2→List Bool}
    {steps : TermJob B1 B2→ℕ} {d e : ℕ}
    (hi : JobPrice (fun r=>(input r).length) d) (hs : JobPrice steps e)
    (K : Callee) (V M : ℕ) :
    JobPrice (fun r=>StageFormulaMetadata.finiteBudget K V M (input r) (steps r))
      (2*d+e) := by
  have hword:=hi.add ((JobPrice.constant 1).raise (Nat.zero_le d))
  have hsteps:=hs.add ((JobPrice.constant 1).raise (Nat.zero_le e))
  have hp:=((JobPrice.constant (100000000*(V+M+TSK K+10))).mul
    (hword.pow 2)).mul hsteps
  have hp' : JobPrice (fun r=>(100000000*(V+M+TSK K+10))*
      ((input r).length+1)^2*(steps r+1)) (2*d+e) := by
    simpa only [zero_add,Nat.mul_comm d 2] using hp
  exact hp'.mono (fun r=>finiteBudget_product_bound K V M (input r) (steps r))

end NearQuarticWires.StageCertNative
