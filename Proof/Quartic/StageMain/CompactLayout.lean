import Proof.Quartic.StageMain.CompactPrepare

/-!
# The finite prefix of the main sampling source

Step 4 of `sec:algorithm`, paper/paper.tex,
uses the same original call, selected parameters and witness prefix
as Steps 1–3. The certificate bitmap and chosen seed follow that
finite prefix and are not part of a per-sample request.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

theorem prepWord_eq_compact {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    Program.prepWord B1 B2 c w = compactInput c p.1 (Program.witnessPrefix c p.1 w) := by
  unfold Program.prepWord Program.stageWord
  rw [hd]
  simp only [compactInput, StageLift.preparedPrefixWord, List.cons_append, List.append_assoc]

theorem greedyWord_compact_layout {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    Program.greedyWord B1 B2 c w =
      compactInput c p.1 (Program.witnessPrefix c p.1 w) ++
      frame (Program.certifiedBits (Program.runCall c p w)) ++
      bitWord (Program.consistentBit (Program.runCall c p w)) ++
      frame (Program.runCall c p w).chosenSeed := by
  unfold Program.greedyWord Program.stageWord
  rw [hd]
  simp only [compactInput, StageLift.preparedPrefixWord, List.cons_append, List.append_assoc]

end NearQuarticWires.StageMain.Compact
