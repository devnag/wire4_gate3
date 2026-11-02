import Proof.Quartic.StageGamma.CompactKernel

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

attribute [local irreducible] kernelCapacities

/-- `prop:time`, paper/paper.tex: every actual
nonblank Gaussian input word has length linear in the seed length. -/
theorem compactKernelInput_length_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (i : Fin 31) :
    (compactKernelInput request choice i).length ≤
      100 * (Cycle.seedLength request.parameters + 9) := by
  have hell : request.parameters.ell ≤ Cycle.seedLength request.parameters := by
    dsimp [Cycle.seedLength]
    omega
  have hk := request.parameters.k_le
  have hp := request.prefixFits
  have hlen : (conjunction request choice).length ≤ 8 := Cycle.gammaChoiceCons_length _ _ _
  have hcs : (SeedFix.consTape request.parameters.ell (2 * request.parameters.kh)
      (conjunction request choice) []).length ≤
      8 * (2 * request.parameters.ell + 4 * request.parameters.kh + 3) + 1 := by
    simp only [SeedFix.consTape, List.length_append, List.length_cons, List.length_nil,
      SeedFix.flatMap_consRec_length, SeedFix.recLen]
    have hm := Nat.mul_le_mul_right
      (2 * request.parameters.ell + 2 * (2 * request.parameters.kh) + 3) hlen
    nlinarith
  fin_cases i <;>
    simp [compactKernelInput, blankKernelPort, kernelInput, SeedFix.bank31,
      initialRegisters, NearCubicWires.RepairOrdinary.ZeroPadding.pad, frame_length, binary_length]
  all_goals omega

end NearQuarticWires.StageGamma
