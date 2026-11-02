import Proof.Quartic.StagePrintTuple.CostContracts

set_option autoImplicit false

namespace NearQuarticWires.StageTupleCensusBounds

open NearCubicGates.Close.Dispatch

/-- `prop:time`, paper/paper.tex: the actual
small-packet binary compiler, including initialization and all head
returns, is linear in source steps times its finite local width polynomial. -/
theorem dispatch_budget (V L N : ℕ) :
    budgetOf V 4 L N≤10^8*(V+2)*(L+1)^8*(N+1) := by
  unfold budgetOf setupCost KC wdOf
  ring_nf
  omega

end NearQuarticWires.StageTupleCensusBounds
