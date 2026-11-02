import Proof.Quartic.StagePrep.CanonicalExitCost
import Proof.Quartic.StagePrep.ClosedCost

/-!
# The all-call preparation clock

Paper: normalized calls in `thm:counter`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open Classical

/-- The exact guarded preparation charge of `prop:time`,
paper/paper.tex. Rejected normalization and
zero-wire calls allocate no canonical parameter computation. -/
noncomputable def rawPreparationCost (B1 B2 Wd : ℕ) (c : Call) : ℕ :=
  frontCost B1 B2 (callWord c).length +
    (if Transfer.Admitted4 B1 B2 c then
      if Transfer.callWires c=0 then
        oddCostT (callWord c).length c.parity.length Wd+2*closedZeroWordLen+50
      else canonicalExitCost c Wd
    else 0)+200

/-- A single original-call envelope for every preparation
exit in `prop:time`, paper/paper.tex. -/
def rawPreparationMajorant (B1 B2 K L : ℕ) : ℕ :=
  frontCost B1 B2 L+oddCostT L L (wdOf K L)+2*closedZeroWordLen+50+
    canonicalBudgetMajorant B1 L+successOutputMajorant L (wdOf K L)+500

/-- The actual preparation charge on every call and every
witness is bounded by the same original-input envelope,
`prop:time`, paper/paper.tex. -/
theorem rawPreparationCost_le (B1 B2 K : ℕ) (c : Call) :
    rawPreparationCost B1 B2 (wdOf K (callWord c).length) c ≤
      rawPreparationMajorant B1 B2 K (callWord c).length := by
  unfold rawPreparationCost
  by_cases ha : Transfer.Admitted4 B1 B2 c
  · rw [if_pos ha]
    by_cases hW : Transfer.callWires c=0
    · rw [if_pos hW]
      have hlen := parity_length_le_callWord c
      have ho : oddCostT (callWord c).length c.parity.length (wdOf K (callWord c).length) ≤
          oddCostT (callWord c).length (callWord c).length (wdOf K (callWord c).length) := by
        unfold oddCostT oddCost
        gcongr
      unfold rawPreparationMajorant
      omega
    · rw [if_neg hW]
      have hc := canonicalExitCost_le B1 B2 c (wdOf K (callWord c).length) ha hW
      unfold rawPreparationMajorant
      omega
  · rw [if_neg ha]
    unfold rawPreparationMajorant
    omega

/-- The common all-call preparation envelope is polynomial
in the original call length, `prop:time`, paper/paper.tex. -/
theorem rawPreparationMajorant_poly (B1 B2 K : ℕ) :
    PolyB (rawPreparationMajorant B1 B2 K) := by
  have hf : PolyB (frontCost B1 B2) := by unfold frontCost; polyb
  have ho : PolyB (fun L => oddCostT L L (wdOf K L)) := by
    unfold oddCostT oddCost wdOf
    polyb
  have hp := PolyB.add
    (PolyB.add
      (PolyB.add
        (PolyB.add (PolyB.add (PolyB.add hf ho) (PolyB.const (2*closedZeroWordLen)))
          (PolyB.const 50))
        (canonicalBudgetMajorant_poly B1))
      (successOutputMajorant_poly K))
    (PolyB.const 500)
  exact hp

end NearQuarticWires.StagePrep
