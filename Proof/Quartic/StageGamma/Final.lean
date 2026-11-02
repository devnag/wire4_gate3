import Proof.Quartic.Cells.ParametersGammaRuntimeFast

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the complete
ORIGINAL coefficient machine has a fixed multiplicative running-time
constant for each fixed pair of counter parameters. -/
noncomputable def gammaCostConstant (B1 B2 : ℕ) : ℕ :=
  Classical.choose (Cells.gammaBudget_selected_fast B1 B2)

/-- `prop:time`, paper/paper.tex: the polynomial
arity exponent is fixed before the ORIGINAL request and closed walk. -/
noncomputable def gammaCostExponent (B1 B2 : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Cells.gammaBudget_selected_fast B1 B2))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the actual cold ORIGINAL-codec machine has exactly the
eighth-power selected coefficient census times a fixed arity polynomial,
in the literal cost shape consumed by the greedy subroutine interface. -/
theorem gammaCost {B1 B2 : ℕ} (q : Greedy.ChildRequest B1 B2)
    (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    gammaBudget (Greedy.gammaRequest q w) ≤
      gammaCostConstant B1 B2 * (q.selected.1.Q + 1) ^ (2 * Algorithm.traceOrder) *
        (q.call.n + 1) ^ gammaCostExponent B1 B2 :=
  Classical.choose_spec (Classical.choose_spec (Cells.gammaBudget_selected_fast B1 B2)) q w

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the ORIGINAL signed coefficient obligation is realized by
the concrete cold machine, with its full actual physical budget. -/
theorem gammaProgramObligation : Machine.GammaProgramObligation gammaBudget :=
  ⟨gammaWordFunction⟩

end NearQuarticWires.StageGamma
