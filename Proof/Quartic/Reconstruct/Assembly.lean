import Proof.Quartic.Reconstruct.TotalProgStage
import Proof.Quartic.Reconstruct.BatchLoopSolved

/-!
# The reconstruction from its stages

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

For a word function `P` computing the print inputs of the tables (the stage `prints`), `phasesOf P` gathers the five
stages of `ReconstructPhases` with the common constant and exponent the largest of theirs: `P`, the printed tables
(`Batch.tablesStage`), the exact systems (`systemsStage`: the gathering `GatherProg.gatherAt` and the emission
`emitStage`, composed by `systemsOfSplit`), the answers (`Batch.solvedStage`) and their sum
(`TotalProg.totalStage`). `reconstructControl_of_prints P` is the reconstruction control of `P`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces.Formats (SysReq SolveMachine sysWord solveWord)

variable {B1 B2 : ℕ}

theorem budget_mono {K K' e e' : ℕ} (hK : K ≤ K') (he : e ≤ e') (n c : ℕ) :
    K * (n + 1) ^ e * c ≤ K' * (n + 1) ^ e' * c :=
  Nat.mul_le_mul (Nat.mul_le_mul hK (Nat.pow_le_pow_right (by omega) he)) le_rfl

/-- The common constant of the two parts of the systems stage. -/
noncomputable def splitK (B1 : ℕ) : ℕ := max (GatherProg.gatherK B1) (emitK B1)

/-- The common exponent of the two parts of the systems stage. -/
def splitE (B1 : ℕ) : ℕ := max (GatherProg.gatherE B1) (emitE B1)

/-- **The systems stage** `tablesWord ↦ frame systemsWord`: the gathering and the emission. -/
noncomputable def systemsStage (B1 B2 : ℕ) :
    WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (systemsWord q))
      (fun q => (8 * splitK B1 + 12) * (q.call.n + 1) ^ splitE B1 * systemsCost q) :=
  systemsOfSplit (splitK B1) (splitE B1)
    (GatherProg.gatherAt B1 B2 _ _ (le_max_left _ _) (le_max_left _ _))
    (WordFunction.enlargeBudget (emitStage B1 B2) fun _ =>
      budget_mono (le_max_right _ _) (le_max_right _ _) _ _)

/-- The common constant of the five stages. -/
noncomputable def asmK (B1 Kp : ℕ) : ℕ :=
  max Kp (max (Batch.batchK B1) (max (8 * splitK B1 + 12) (max (Batch.solvedK B1) (TotalProg.totalK B1))))

/-- The common exponent of the five stages. -/
noncomputable def asmE (B1 B2 ep : ℕ) : ℕ :=
  max ep (max (Batch.batchE B1) (max (splitE B1) (max (Batch.solvedE B1 B2) (TotalProg.totalE B1))))

/-- **The five stages of the reconstruction** from the stage `prints`. -/
noncomputable def phasesOf {Kp ep : ℕ}
    (P : WordFunction (ChildRequest B1 B2) gammaWord (fun q => frame (printsWord q))
      (fun q => Kp * (q.call.n + 1) ^ ep * printsCost q)) : ReconstructPhases B1 B2 where
  K := asmK B1 Kp
  e := asmE B1 B2 ep
  prints := WordFunction.enlargeBudget P fun _ => budget_mono (le_max_left _ _) (le_max_left _ _) _ _
  tables := fun printBudget printBound print hprint =>
    WordFunction.enlargeBudget (Batch.tablesStage B1 B2 printBudget printBound print hprint) fun _ =>
      budget_mono (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) (le_max_right _ _)) _ _
  systems := WordFunction.enlargeBudget (systemsStage B1 B2) fun _ =>
    budget_mono (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) _ _
  solved := fun solver solveBound hsolve =>
    WordFunction.enlargeBudget (Batch.solvedStage B1 B2 solver solveBound hsolve) fun _ =>
      budget_mono
        (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _))
        (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _))
        _ _
  total := fun solver solveBound hsolve =>
    WordFunction.enlargeBudget (TotalProg.totalStage B1 B2 solver solveBound hsolve) fun _ =>
      budget_mono
        (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _))
        (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _))
        _ _

/-- **The reconstruction control from the stage `prints`.** -/
noncomputable def reconstructControl_of_prints {Kp ep : ℕ}
    (P : WordFunction (ChildRequest B1 B2) gammaWord (fun q => frame (printsWord q))
      (fun q => Kp * (q.call.n + 1) ^ ep * printsCost q)) : ReconstructControl B1 B2 :=
  (phasesOf P).control

end NearQuarticWires.Reconstruct
