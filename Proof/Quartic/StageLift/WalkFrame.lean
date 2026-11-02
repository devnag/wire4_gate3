import Proof.Quartic.StageLift.SourceOutputState
import Proof.Quartic.StageLift.SourceBudget

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: each literal
walk payload is physically marked and terminated after its raw scalar
headers, without copying any already emitted output front. -/
def emitFramedWalkPayload : St VV MM := StageRecovery.OutputFrame.framedProgram emitWalkPayload

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual complete walk source is framed with every
marker and delimiter charged, preserving all original source state. -/
theorem emitFramedWalkPayload_spec {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) (a : DS VV MM)
    (ha : WalkSourceState (printSourceContext B1 B2 (Greedy.printInput r)) r index.val a)
    (hi : a.env printWalkIndex = index.val) :
    let C := printSourceContext B1 B2 (Greedy.printInput r)
    Hs C emitFramedWalkPayload a (3 * walkPayloadCost r C.Lk C.Bk + 2) (fun z =>
      z.out = a.out ++ frame ((toks (sourceWalkFormula r index)).flatMap tokWord) ∧
      WalkSourceState C r (index.val + 1) z ∧ z.env printWalkIndex = index.val ∧ z.ip = a.ip) := by
  dsimp only
  let C := printSourceContext B1 B2 (Greedy.printInput r)
  let start : DS VV MM := { a with out := [] }
  have hstart : WalkSourceState C r index.val start := ha.withOutput []
  obtain ⟨b,n,he,hn,hbo,hbstate,hbI,hbip⟩ := emitWalkPayload_spec r index start hstart hi
  have hex := framedProgram_afterPrefix he (by rfl) a.out
  have hinit : { start with out := a.out } = a := by cases a; rfl
  rw [hinit] at hex
  let z : DS VV MM := { b with out := a.out ++ frame b.out }
  have hzstate : WalkSourceState C r (index.val + 1) z := hbstate.withOutput _
  refine ⟨z,3*n+2,hex,by omega,?_,hzstate,hbI,hbip⟩
  change a.out ++ frame b.out = _
  change b.out = [] ++ (toks (sourceWalkFormula r index)).flatMap tokWord at hbo
  rw [hbo, List.nil_append]

end NearQuarticWires.StageLift
