import Proof.Quartic.StageNativeKids.Cost
import Proof.Quartic.StagePrintTuple.TermStageContract

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

/-- `prop:time`, paper/paper.tex: the
complete concrete native-provider budget satisfies the actual monomial
controller's positive fixed-coefficient and positive fixed-exponent
source-price field, with the identical budget and no extra premise. -/
theorem nativeStagePrice : StageTuple.NativeStagePrice NativeKidsRequest.budget := by
  obtain ⟨K, E, h⟩ := budget_polynomial
  refine ⟨K + 1, E + 1, by omega, by omega, fun r => ?_⟩
  have hs : 1 ≤ r.word.length + r.header.call.n + r.outputWidth + 1 := by omega
  exact (h r).trans (Nat.mul_le_mul (Nat.le_succ _)
    (Nat.pow_le_pow_right hs (Nat.le_succ E)))

end NearQuarticWires.StageNativeKids
