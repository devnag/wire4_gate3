import Proof.Quartic.StageMain.RuntimeSizes
import Proof.Quartic.StageCertTests.ParameterReadCost

/-!
# Cost of decoding the finite main source

`sec:params`, paper/paper.tex, and `prop:time`: the actual counted parameter reader is charged by its
serialized fields. The common main width bounds both its source length
and its arithmetic bit-length parameter.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open Compact Bounds StageLift

theorem selected_parameterReadCost {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    parameterReadCost p.1 (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤
      20000 * (runtimeScale f K d c.n) ^ 2 := by
  let S := runtimeScale f K d c.n
  have hS : 1 ≤ S := by dsimp only [S, runtimeScale]; omega
  have hc : (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤ S := by
    have hh := (compact_le K d hd w).trans (runtimeScale_envelope f K d c.n)
    rwa [prepWord_eq_compact hd] at hh
  have hp : (Program.parametersWord p.1).length ≤ S := by
    apply le_trans (b := (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length) ?_ hc
    simp only [compactInput, preparedPrefixWord, List.length_append, List.length_cons]
    omega
  calc
    _ ≤ 5000 * ((Program.parametersWord p.1).length + 1) *
        ((compactInput c p.1 (Program.witnessPrefix c p.1 w)).length + 1) :=
      StageCertTests.parameterReadCost_le_word _ _
    _ ≤ 5000 * (S + 1) * (S + 1) := by gcongr
    _ ≤ _ := by change _ ≤ 20000 * S ^ 2; nlinarith only [hS]

end NearQuarticWires.StageMain.Runtime
