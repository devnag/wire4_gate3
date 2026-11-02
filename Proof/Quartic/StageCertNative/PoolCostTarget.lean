import Proof.Quartic.StageCertNative.PriceBasic
import Proof.Quartic.StageCertNative.PriceCuts
import Proof.Quartic.StageCertNative.WholeWeak

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: the actual
once-context source, counted original term loop and signed payload
concatenation fit one original-column envelope. The displayed local
degree hypothesis is discharged by the concrete per-term compiler;
it is not an extra input to the final certificate machine. -/
def WholeWeakCostClaim (B1 B2 : ℕ) : Prop :=
  ∀termBudget : TermJob B1 B2→ℕ,JobPrice termBudget 4→
    ∃K E : ℕ,∀r : IndexedRequest B1 B2,
      wholeWeakOriginalBudget (termBudget:=termBudget) r≤
        K*(r.prepared.call.n+1)^E*
          2^(r.prepared.call.n-r.prepared.selected.1.k)

end NearQuarticWires.StageCertNative
