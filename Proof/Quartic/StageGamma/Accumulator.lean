import Proof.Quartic.StageGamma.IntegerBounds
import Proof.Gates.WordPrograms.SInt

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open scoped BigOperators
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicGates.Close.WordPrograms

/-- `cor:conditional`, paper/paper.tex: the scaled
signed partial sum over the exact choices already visited. -/
noncomputable def scaledAccumulator (request : Machine.GammaRequest)
    (T : Finset (Cycle.GammaChoice request.parameters.Q)) : ℤ :=
  (2 : ℤ) ^ request.prefixLength * ∑ choice ∈ T, expansionTerm request choice

/-- `cor:conditional`, paper/paper.tex: the fixed
binary magnitude width funds every partial sum, irrespective of signs. -/
def accumulatorWidth (request : Machine.GammaRequest) : ℕ :=
  4 * Cycle.seedLength request.parameters + 9

/-- `cor:conditional`, paper/paper.tex: inserting one
fresh exact choice updates the actual signed numerator. -/
theorem scaledAccumulator_insert (request : Machine.GammaRequest)
    (T : Finset (Cycle.GammaChoice request.parameters.Q))
    (choice : Cycle.GammaChoice request.parameters.Q) (hchoice : choice ∉ T) :
    scaledAccumulator request (insert choice T) = scaledAccumulator request T +
      (2 : ℤ) ^ request.prefixLength * expansionTerm request choice := by
  unfold scaledAccumulator
  rw [Finset.sum_insert hchoice]
  ring

/-- `cor:conditional`, paper/paper.tex: the actual
physical signed adder handles a new Gaussian contribution. Every overflow
condition follows from the original seed and exact choice census. -/
theorem accumulateTerm_run {ns nr : ℕ} (request : Machine.GammaRequest)
    (T : Finset (Cycle.GammaChoice request.parameters.Q))
    (choice : Cycle.GammaChoice request.parameters.Q) (hchoice : choice ∉ T)
    (ACC TERM M N : Fin (ns + 1)) (S U F R : Fin nr)
    (hs : [ACC, TERM, M, N].Nodup) (hr : [S, U, F, R].Nodup)
    (σ : WState ns nr) (m0 n0 : ℕ)
    (hacc : SInt.SNumOn σ ACC (accumulatorWidth request) (scaledAccumulator request T))
    (hterm : SInt.SNumOn σ TERM (accumulatorWidth request)
      ((2 : ℤ) ^ request.prefixLength * expansionTerm request choice))
    (hm : NumOn σ M (accumulatorWidth request + 1) m0)
    (hn : NumOn σ N (accumulatorWidth request + 1) n0)
    (hS : σ.val S = 0) (hU : σ.val U = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) :
    Runs (2 * (accumulatorWidth request + 1) + 1)
      (SInt.sadd ACC TERM M N S U F R) σ (410 * accumulatorWidth request + 600)
      (SInt.OpPost σ ACC M N (accumulatorWidth request)
        (scaledAccumulator request (insert choice T))) := by
  have hb : (scaledAccumulator request T +
      (2 : ℤ) ^ request.prefixLength * expansionTerm request choice).natAbs <
      2 ^ accumulatorWidth request := by
    rw [← scaledAccumulator_insert request T choice hchoice]
    exact scaledPartial_fits request (insert choice T)
  simpa only [← scaledAccumulator_insert request T choice hchoice] using
    SInt.sadd_spec (2 * (accumulatorWidth request + 1) + 1) (accumulatorWidth request)
      hs hr σ (scaledAccumulator request T)
      ((2 : ℤ) ^ request.prefixLength * expansionTerm request choice) m0 n0
      hacc hterm hm hn hS hU hF hR hb le_rfl

/-- `cor:conditional`, paper/paper.tex: after all exact
choices have been accumulated, the result is the original requested Gamma. -/
theorem scaledAccumulator_univ (request : Machine.GammaRequest) :
    scaledAccumulator request Finset.univ = Machine.gammaTarget request := by
  rw [Machine.gammaTarget, Cycle.scaledGamma_gauss request.parameters request.prefixLength
    request.prefixCode request.prefixFits request.walk]
  rfl

end NearQuarticWires.StageGamma
