import Proof.Quartic.StageTupleSetupCold.Machine
import Proof.Quartic.StageTupleSetupCost.Final

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

/-- `lem:print` and `prop:time`, paper/paper.tex: the very same complete cold
machine budget is additive linear in the entire unchanged source
and polynomial in the separate structural magnitude. Terms and their
length occur only in the linear source summand. -/
theorem setupBudget_linear_source : StageTuple.TupleSetupCost setupBudget :=
  StageTupleSetupCost.setupBudget_linear_source

end NearQuarticWires.StageTupleSetupCold
