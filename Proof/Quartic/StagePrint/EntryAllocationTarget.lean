import Proof.Quartic.StagePrint.EntrySizing
import Proof.Quartic.StageRecovery.PacketMachine

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print` and `prop:time`, paper/paper.tex: fixed original-arity allocation covers the real
arithmetic and logarithmic source heights, and the actual compiled
clock is linear in finite source and execution lengths. -/
structure Allocation (C E : ℕ) (modular : Bool) where
  sizes : Sz
  required : ∀ r : BoundedRequest C E modular,
    r.toRequest.sizingMagnitude+10 ≤ sizes.W (leadOnes r.word)
  linear_budget : ∃ K e : ℕ,∀ (r : BoundedRequest C E modular) (steps : ℕ),
    langBudget StageRecovery.packetCallee sizes VV MM r.word steps≤
      K*(r.word.length+steps+1)*(r.header.call.n+1)^e

end NearQuarticWires.StagePrint.EntryFormat
