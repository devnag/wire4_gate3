import Proof.Quartic.StageNativeKids.AcquireRun

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

attribute [local irreducible] framedRoleWordFunction

/-- `prop:time`, paper/paper.tex: the
ordinary source-acquisition budget includes all actual source and role
work plus the charged final ordinary tape and register return. -/
noncomputable def acquireBudget (r : NativeKidsRequest) : ℕ := 2 * acquireClock r + 2

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual original eleven-field request
produces the exact acquired eleven-field record in one outer frame.
The original source, binary context, atom and width remain unchanged;
the sixth field is the computed original occurrence and affine header. -/
noncomputable def acquireWordFunction :
    WordFunction NativeKidsRequest NativeKidsRequest.word
      (fun r => frame r.acquiredWord) acquireBudget :=
  wordFunction_of_ideal acquireProgram
    (acquireOutput framedRoleWordFunction.program.tapeCount)
    (by change 15 + framedRoleWordFunction.program.tapeCount ≠ 0; omega)
    acquireCapacity acquireLens acquireClock (fun _ => le_rfl) (by
      intro r
      refine ⟨?_, acquire_run r⟩
      have h13 : 15 + framedRoleWordFunction.program.tapeCount ≠ 13 := by omega
      simp [acquireLens, acquireOutput, h13])

end NearQuarticWires.StageNativeKids
