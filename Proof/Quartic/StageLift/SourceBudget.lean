import Proof.Quartic.StageLift.ColdStartup
import Proof.Quartic.StageLift.WalkPayload

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print` and `prop:time`, paper/paper.tex: the four actual binary headers precede a physically
framed complete walk payload, with each marker and sequence charged. -/
noncomputable def walkPacketCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (L B : ℕ) : ℕ :=
  1600 * (sourceEnvelope r + 1) ^ 2 + 3 * walkPayloadCost r L B + 176

/-- Step 3 and `prop:time`, paper/paper.tex: every original walk is processed once by the actual
bounded loop, including its initialization, tests and increments. -/
noncomputable def allWalkSourceCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (L B : ℕ) : ℕ :=
  r.child.cellCall.seed.N ^ 8 * (walkPacketCost r L B + 4) + 4

/-- Step 3 and `prop:time`, paper/paper.tex: the actual cold source clock includes original input
acquisition, one raw preparation carrier, the full all-walk stream and
all real source-callee reservations. Raw indices are processed once. -/
noncomputable def sourceProgramSteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  let C := printSourceContext B1 B2 (Greedy.printInput r)
  carrierStartupCost r + 6 + allWalkSourceCost r C.Lk C.Bk + 1

/-- `prop:time`, paper/paper.tex: the physical
ordinary-machine source budget includes actual language compilation,
header allocation, structural callees, head returns and teardown. -/
noncomputable def sourceMachineBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  langBudget (StageCert.Tokens.structuralSourceCallee B1 B2) (printSourceSizes B1 B2)
    VV MM (Greedy.printInput r) (sourceProgramSteps r)

/-- `lem:print` and `prop:time`, paper/paper.tex: exact selected source cost, with raw indices paid
additively once and the original degree reserve unchanged. -/
def sourceMachineBudgetSelectedSpec (B1 B2 : ℕ) : Prop :=
  ∃ K e : ℕ, ∀ r : Greedy.PrintRequest B1 B2,
    sourceMachineBudget r ≤ K *
      (2 ^ (r.child.call.n - r.child.selected.1.k) * (r.child.call.n + 1) ^ e +
        ((Greedy.printIndexWord r).length + 1) ^ e)

end NearQuarticWires.StageLift
