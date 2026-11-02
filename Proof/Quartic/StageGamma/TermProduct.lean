import Proof.Quartic.StageGamma.Accumulator

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open scoped BigOperators
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicGates.Close.WordPrograms

/-- `cor:conditional`, paper/paper.tex: the exact
nonnegative Gaussian count with the original prefix scale restored. -/
noncomputable def scaledGaussCount (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : ℤ :=
  (2 : ℤ) ^ request.prefixLength *
    ((JoinElimination.condProbGauss request.parameters.modulus request.parameters.ell 8
      (2 * request.parameters.kh) request.prefixLength request.prefixCode
      (conjunction request choice)).1 : ℤ)

/-- `cor:conditional`, paper/paper.tex: multiplying
the signed eight-slot coefficient by the actual Gaussian count gives
precisely this term's contribution to the original numerator. -/
theorem scaledTerm_product (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    Cycle.gammaChoiceWeight request.parameters.N request.parameters.Q choice *
      scaledGaussCount request choice =
    (2 : ℤ) ^ request.prefixLength * expansionTerm request choice := by
  unfold scaledGaussCount expansionTerm
  ring

/-- `cor:conditional` and `prop:time`, paper/paper.tex: an actual physical signed multiplier forms each selected
contribution, and the original choice census discharges its overflow bound. -/
theorem multiplyTerm_run {ns nr : ℕ} (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q)
    (WEIGHT COUNT M N C D : Fin (ns + 1)) (S T F R G : Fin nr)
    (hs : [WEIGHT, COUNT, M, N, C, D].Nodup) (hr : [S, T, F, R, G].Nodup)
    (σ : WState ns nr) (m0 n0 c0 d0 : ℕ)
    (hweight : SInt.SNumOn σ WEIGHT (accumulatorWidth request)
      (Cycle.gammaChoiceWeight request.parameters.N request.parameters.Q choice))
    (hcount : SInt.SNumOn σ COUNT (accumulatorWidth request) (scaledGaussCount request choice))
    (hm : NumOn σ M (accumulatorWidth request + 1) m0)
    (hn : NumOn σ N (accumulatorWidth request + 1) n0)
    (hc : NumOn σ C (accumulatorWidth request + 1) c0)
    (hd : NumOn σ D (accumulatorWidth request + 1) d0)
    (hS : σ.val S = 0) (hT : σ.val T = 0) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hG : σ.val G = 0) :
    Runs (2 * (accumulatorWidth request + 1) + 1)
      (SInt.smul WEIGHT COUNT M N C D S T F R G) σ
      (SInt.smulCost (accumulatorWidth request))
      (fun τ => SInt.SNumOn τ WEIGHT (accumulatorWidth request)
          ((2 : ℤ) ^ request.prefixLength * expansionTerm request choice) ∧
        (∃ m, NumOn τ M (accumulatorWidth request + 1) m) ∧
        (∃ n, NumOn τ N (accumulatorWidth request + 1) n) ∧
        (∃ c, NumOn τ C (accumulatorWidth request + 1) c) ∧
        (∃ d, NumOn τ D (accumulatorWidth request + 1) d) ∧
        SameExcept σ τ [WEIGHT, M, N, C, D] []) := by
  have hb : (Cycle.gammaChoiceWeight request.parameters.N request.parameters.Q choice *
      scaledGaussCount request choice).natAbs < 2 ^ accumulatorWidth request := by
    rw [scaledTerm_product]
    simpa [accumulatorWidth] using
      scaledPartial_fits request ({choice} : Finset (Cycle.GammaChoice request.parameters.Q))
  simpa only [scaledTerm_product] using
    SInt.smul_spec (2 * (accumulatorWidth request + 1) + 1) (accumulatorWidth request)
      hs hr σ (Cycle.gammaChoiceWeight request.parameters.N request.parameters.Q choice)
      (scaledGaussCount request choice) m0 n0 c0 d0 hweight hcount hm hn hc hd
      hS hT hF hR hG hb le_rfl

/-- `prop:time`, paper/paper.tex: the genuine signed
product has quadratic work in the original seed length. -/
theorem multiplyTermCost_le (request : Machine.GammaRequest) :
    SInt.smulCost (accumulatorWidth request) ≤
      10000 * (Cycle.seedLength request.parameters + 9) ^ 2 := by
  dsimp [SInt.smulCost, accumulatorWidth]
  nlinarith

end NearQuarticWires.StageGamma
