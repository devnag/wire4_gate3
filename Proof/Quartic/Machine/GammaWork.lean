import Proof.Quartic.Machine.GammaInterface
import Proof.Quartic.Cycle.GammaGauss
import Proof.Wire_3_5.SeedFixElim
import Proof.Wire_3_5.GF2Primitive

set_option autoImplicit false

namespace NearQuarticWires.Machine

open scoped BigOperators

/-- `cor:conditional`, paper/paper.tex: the actual existing
row-construction/Gaussian primitive cost for ONE unpadded expansion choice.
The field modulus is cached; no primitive-field search occurs here. -/
noncomputable def gammaGaussIterationCost (request : GammaRequest)
    (choice : NearQuarticWires.Cycle.GammaChoice request.parameters.Q) : ℕ :=
  NearCubicWires.WireExponent3_5.SeedFix.elimCost request.parameters.ell 8
    (2 * request.parameters.kh) request.prefixLength
    (NearQuarticWires.Cycle.gammaChoiceCons request.parameters request.walk choice).length

/-- `cor:conditional`, paper/paper.tex: the Gaussian
kernel is polynomial in the seed length, including repeated sample labels.
The bound charges one Gaussian elimination invocation. -/
theorem gammaGaussIterationCost_le (request : GammaRequest)
    (choice : NearQuarticWires.Cycle.GammaChoice request.parameters.Q) :
    gammaGaussIterationCost request choice ≤
      3000 * (NearQuarticWires.Cycle.seedLength request.parameters + 9) ^ 6 := by
  have hlen :
      (NearQuarticWires.Cycle.gammaChoiceCons request.parameters request.walk choice).length ≤ 8 := by
    unfold NearQuarticWires.Cycle.gammaChoiceCons
    simpa using List.length_filterMap_le _ (List.finRange 8)
  have hell : request.parameters.ell ≤ NearQuarticWires.Cycle.seedLength request.parameters := by
    unfold NearQuarticWires.Cycle.seedLength
    omega
  have h8 : 8 ≤ NearQuarticWires.Cycle.seedLength request.parameters := by
    unfold NearQuarticWires.Cycle.seedLength
    have hp := request.parameters.one_le_ell
    omega
  unfold gammaGaussIterationCost
  apply NearCubicWires.WireExponent3_5.SeedFix.elimCost_le
  · omega
  · omega
  · omega
  · have hk := request.parameters.k_le
    omega
  · omega
  · exact request.prefixFits

/-- `prop:time`, paper/paper.tex: the Gaussian kernels over all
EXACT `(Q+1)^8` choices; decoder, signed accumulator and loop overhead
still need their separate physical machine bounds. -/
noncomputable def gammaGaussKernelWork (request : GammaRequest) : ℕ :=
  ∑ choice : NearQuarticWires.Cycle.GammaChoice request.parameters.Q,
    gammaGaussIterationCost request choice

/-- `prop:time`, paper/paper.tex: the proved primitive costs sum
with the unpadded choice census, not with all field labels. -/
theorem gammaGaussKernelWork_le (request : GammaRequest) :
    gammaGaussKernelWork request ≤ (request.parameters.Q + 1) ^ 8 *
      (3000 * (NearQuarticWires.Cycle.seedLength request.parameters + 9) ^ 6) := by
  unfold gammaGaussKernelWork
  calc
    (∑ choice : NearQuarticWires.Cycle.GammaChoice request.parameters.Q,
        gammaGaussIterationCost request choice) ≤
        ∑ _choice : NearQuarticWires.Cycle.GammaChoice request.parameters.Q,
          3000 * (NearQuarticWires.Cycle.seedLength request.parameters + 9) ^ 6 :=
      Finset.sum_le_sum (fun _ _ => gammaGaussIterationCost_le request _)
    _ = _ := by simp [NearQuarticWires.Cycle.GammaChoice]

/-- `prop:time`, paper/paper.tex: explicit field-modulus search
cost is paid in setup, once, and is not called a polynomial-time search. -/
theorem gammaFieldSetupCost_le (request : GammaRequest) :
    NearCubicWires.WireExponent3_5.GF2.searchCost request.parameters.ell ≤
      200 * (2 ^ (2 * request.parameters.ell) *
        (NearQuarticWires.Cycle.seedLength request.parameters + 9)) := by
  have hell : request.parameters.ell ≤ NearQuarticWires.Cycle.seedLength request.parameters := by
    unfold NearQuarticWires.Cycle.seedLength
    omega
  simpa only [pow_one] using
    NearCubicWires.WireExponent3_5.GF2.searchCost_le request.parameters.ell
      (NearQuarticWires.Cycle.seedLength request.parameters + 9) (by omega) (by omega)

end NearQuarticWires.Machine
