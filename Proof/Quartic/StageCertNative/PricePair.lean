import Proof.Quartic.StageCertNative.PriceBasic
import Proof.Quartic.StageRecovery.FramedPair

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: joining two
computed framed fields is linear in both actual call clocks and in
the three finite word lengths. -/
theorem JobPrice.framedPair {B1 B2 : ℕ}
    {input left right : TermJob B1 B2→List Bool}
    {lb rb : TermJob B1 B2→ℕ} {d : ℕ}
    (hi : JobPrice (fun r=>(input r).length) d)
    (hl : JobPrice (fun r=>(left r).length) d)
    (hr : JobPrice (fun r=>(right r).length) d)
    (hbl : JobPrice lb d) (hbr : JobPrice rb d) :
    JobPrice (fun r=>2*StageRecovery.FramedPair.cost (input:=input) (left:=left)
      (right:=right) (lb:=lb) (rb:=rb) r+2) d := by
  have h2l : JobPrice (fun r=>2*lb r) d := by
    simpa only [zero_add] using (JobPrice.constant 2).mul hbl
  have h2r : JobPrice (fun r=>2*rb r) d := by
    simpa only [zero_add] using (JobPrice.constant 2).mul hbr
  have hs:=((hi.add hl).add hr).add ((JobPrice.constant 1).raise (Nat.zero_le d))
  have h300 : JobPrice (fun r=>300*((input r).length+(left r).length+(right r).length+1)) d := by
    simpa only [zero_add] using (JobPrice.constant 300).mul hs
  have hcost:=((h2l.add h2r).add h300)
  have htwice : JobPrice (fun r=>2*(2*lb r+2*rb r+
      300*((input r).length+(left r).length+(right r).length+1))) d := by
    simpa only [zero_add] using (JobPrice.constant 2).mul hcost
  exact htwice.add ((JobPrice.constant 2).raise (Nat.zero_le d))

end NearQuarticWires.StageCertNative
