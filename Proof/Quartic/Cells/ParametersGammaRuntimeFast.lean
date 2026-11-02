import Proof.Quartic.Cells.ParametersGammaRuntimeFastArithmetic
import Proof.Quartic.Greedy.Stage

set_option autoImplicit false

namespace NearQuarticWires.Cells

open StageGamma
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the complete
original-source coefficient machine pays both actual pipe stages,
with its literal eighth-power census and a fixed seed polynomial. -/
theorem gamma_budget_seed_bound_fast {B1 B2 : ℕ} (q : Greedy.ChildRequest B1 B2)
    (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    gammaBudget (Greedy.gammaRequest q w) ≤
      (4 * (10 ^ 16 * (TSK fieldProducerCallee + 1)) +
        4 * (10 ^ 72 * (TSK compactGaussCallee + 1) ^ 2) + 12) *
        ((q.selected.1.Q + 1) ^ 8 *
          (Cycle.seedLength (Greedy.gammaRequest q w).parameters + 9) ^ 24) := by
  have hcompiled := gamma_compiled_cost_bound (Greedy.gammaRequest q w)
  have hQ : (Greedy.gammaRequest q w).parameters.Q = q.selected.1.Q := rfl
  dsimp only at hcompiled
  rw [hQ] at hcompiled
  exact ParameterArithmetic.gamma_pipe_scalar_bound _ _ _ _ _ _ (by omega)
    (Nat.one_le_pow _ _ (Nat.succ_pos _))
    (cachedRequestBudget_selected_le q w) hcompiled

/-- `prop:time`, paper/paper.tex: the actual cold
coefficient budget has exactly the selected `(Q+1)^(2m)` factor
times a fixed original-arity polynomial, for every walk and prefix. -/
theorem gammaBudget_selected_fast (B1 B2 : ℕ) :
    ∃ Kγ eγ : ℕ, ∀ (q : Greedy.ChildRequest B1 B2)
      (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder),
      gammaBudget (Greedy.gammaRequest q w) ≤
        Kγ * (q.selected.1.Q + 1) ^ (2 * Algorithm.traceOrder) *
          (q.call.n + 1) ^ eγ := by
  refine ⟨(4 * (10 ^ 16 * (TSK fieldProducerCallee + 1)) +
    4 * (10 ^ 72 * (TSK compactGaussCallee + 1) ^ 2) + 12) *
      (8 * (2 * B1 + 103) + 9) ^ 24, 24, ?_⟩
  intro q w
  have hseed : Cycle.seedLength (Greedy.gammaRequest q w).parameters =
      Greedy.seedRounds B1 B2 q.call :=
    (Greedy.seedRounds_of_dispatch q.dispatched q.witness).symm
  have hs : Cycle.seedLength (Greedy.gammaRequest q w).parameters ≤
      8 * (2 * B1 + 103) * (q.call.n + 1) :=
    hseed.le.trans (Greedy.seedRounds_le q.call)
  exact ParameterArithmetic.gamma_arity_scalar_bound _ _ _ _ _ _
    (gamma_budget_seed_bound_fast q w) hs

end NearQuarticWires.Cells
