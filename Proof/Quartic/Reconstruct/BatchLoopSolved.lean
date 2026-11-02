import Proof.Quartic.Reconstruct.BatchLoopSolve
import Proof.Quartic.Reconstruct.BatchLoopStages

/-!
# The stage `solved` of the reconstruction

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`: for every
exact solver, the stage maps the systems `systemsWord` to the answers `solvedWord`, one call of the solver per
system (`solvedStage`, the field `ReconstructPhases.solved`). It is the batch `batchP` of the solver's program with
the answer copier (`batchP_exec`, `solveCopier_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Reconstruct.Batch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearQuarticWires.Control
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct
open NearCubicGates.Close.Interfaces (listWord Call)
open NearCubicGates.Close.Interfaces.Formats (SysReq SolveMachine sysWord solveWord)

variable {B1 B2 : ℕ}

/-- The solver as a word function on the systems of a child. -/
def solverOn (S : SolveMachine) (q : ChildRequest B1 B2) :
    WordFunction (SystemIndex q) (fun x => sysWord (systemAt q x)) (fun x => solveWord (S.solve (systemAt q x)))
      (fun x => S.budget (systemAt q x)) :=
  ⟨S.wf.program, fun x => S.wf.realizes (systemAt q x)⟩

/-- The register capacity of the stage `solved`. -/
noncomputable def solvedCap (q : ChildRequest B1 B2) (S : SolveMachine) (B : ℕ) : ℕ :=
  2 ^ ((systemsWord q).length + (solvedWord q S).length + B + 10)

/-- **The stage `solved` on a child.** -/
theorem solvedRun (S : SolveMachine) (solveBound : Call → List Bool → ℕ)
    (hsolve : ∀ (q : ChildRequest B1 B2) (s : SysReq), (sysWord s).length ≤ (q.call.n + 1) ^ sizeExp B1 B2 →
      S.budget s ≤ solveBound q.call q.witness) (q : ChildRequest B1 B2) :
    ∃ τ, WXExec (solvedCap q S (solveBound q.call q.witness)) (batchP S.wf.program (solveCopier S.wf.program))
      (gammaStart _ (systemsWord q)) τ
      (batchCost (RepairRepresentation.natWord q.call.n) (systemTag q) (fun x => sysWord (systemAt q x))
        (fun x => solveWord (S.solve (systemAt q x))) (solveBound q.call q.witness)
        (fun x => solveCopyCost (S.solve (systemAt q x))) (systemList q)) ∧
      τ.st (cOUT _) = frame (solvedWord q S) := by
  have hB : ∀ x ∈ systemList q, S.budget (systemAt q x) ≤ solveBound q.call q.witness :=
    fun x _ => hsolve q _ (sysWord_le_sizeExp q x)
  have hUl : (solvedWord q S).length = (batchOut (RepairRepresentation.natWord q.call.n) (systemTag q)
      (fun x => solveWord (S.solve (systemAt q x))) (systemList q)).length := rfl
  have hWl : (systemsWord q).length = (frame (RepairRepresentation.natWord q.call.n) ++
      listWord (fun x => frame (systemTag q x) ++ frame (sysWord (systemAt q x))) (systemList q)).length := rfl
  exact batchP_exec _ (solverOn S q) (solveCopier S.wf.program) (solveCopier_avoids _) (systemTag q)
    (fun x => solveCopyCost (S.solve (systemAt q x))) (solveBound q.call q.witness)
    (RepairRepresentation.natWord q.call.n) (systemList q) hB
    (fun x hx σ hO hOh hT hR => solveCopier_exec _ _ (S.solve (systemAt q x)) σ hO hOh hT hR (by
      have h1 := output_length_le (solverOn S q) x
      have h2 := hB x hx
      have h3 : 2 ^ ((solveWord (S.solve (systemAt q x))).length + 2) ≤ 2 ^ (solveBound q.call q.witness + 3) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : 2 ^ (solveBound q.call q.witness + 3) * 16 ≤ solvedCap q S (solveBound q.call q.witness) := by
        unfold solvedCap
        calc 2 ^ (solveBound q.call q.witness + 3) * 16 = 2 ^ (solveBound q.call q.witness + 7) := by ring
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : solveBound q.call q.witness + 3 < 2 ^ (solveBound q.call q.witness + 3) := Nat.lt_two_pow_self
      omega))
    (by rw [← hWl, ← hUl]; exact le_two_pow_add _)


/-! ## The cost -/

theorem solve_length_le (S : SolveMachine) (s : SysReq) (F : List ℚ) (h : S.solve s = some F) :
    F.length ≤ (sysWord s).length := by
  have hs := (S.sound s F h).1
  have hc := (listWord_count (listWord NearCubicGates.Close.Interfaces.intWord) s.pts (fun u => by
    have := (listWord_count NearCubicGates.Close.Interfaces.intWord u (fun z => by
      have := natBitLength_le_intWord z; omega)).1; omega)).2
  simp only [sysWord, List.length_append]
  omega

/-- The constant of the stage `solved`. -/
def solvedK (B1 : ℕ) : ℕ :=
  1000000 * (Cells.ParameterArithmetic.preparationCoefficient B1 * Cells.ParameterArithmetic.preparationCoefficient B1 + 3)

/-- The exponent of the stage `solved`. -/
noncomputable def solvedE (B1 B2 : ℕ) : ℕ := 2 * (B1 + 12) + 2 * sizeExp B1 B2 + 1

/-- **One system costs a polynomial in the size.** -/
theorem solvedItem_le (S : SolveMachine) (q : ChildRequest B1 B2) (B : ℕ) (x : SystemIndex q)
    (hout : (solveWord (S.solve (systemAt q x))).length ≤ B + 1) :
    itemCost (systemTag q x).length (sysWord (systemAt q x)).length B (solveCopyCost (S.solve (systemAt q x))) + 2 ≤
      20000 * (envelope q * envelope q + (q.call.n + 1) ^ sizeExp B1 B2 * (q.call.n + 1) ^ sizeExp B1 B2 +
        (q.call.n + 1) ^ sizeExp B1 B2 + 1) * (B + 1) := by
  have hX := sysWord_le_sizeExp q x
  have hTG := systemTag_length_le q x
  have hcp := solveCopyCost_le (S.solve (systemAt q x)) ((q.call.n + 1) ^ sizeExp B1 B2 + 1)
    ((q.call.n + 1) ^ sizeExp B1 B2) (fun F hF => by
      have := solve_length_le S _ F hF
      exact ⟨(natBitLength_le_self_succ _).trans (by omega), by omega⟩)
  set X := (q.call.n + 1) ^ sizeExp B1 B2 with hXd
  set V := envelope q with hVd
  have hp1 : 300 * (X + 1 + 10) * (X + 2) = 300 * (X * X) + 3900 * X + 6600 := by ring
  have hQ : 1 ≤ V * V + X * X + X + 1 := by omega
  have hQB : V * V + X * X + X + 1 ≤ (V * V + X * X + X + 1) * (B + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hBQ : B + 1 ≤ (V * V + X * X + X + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hVQ : V * V ≤ V * V + X * X + X + 1 := by omega
  unfold itemCost callCost cleanCost
  nlinarith

theorem solvedBatch_le (S : SolveMachine) (solveBound : Call → List Bool → ℕ) (q : ChildRequest B1 B2)
    (hB : ∀ x ∈ systemList q, S.budget (systemAt q x) ≤ solveBound q.call q.witness) :
    2 * batchCost (RepairRepresentation.natWord q.call.n) (systemTag q) (fun x => sysWord (systemAt q x))
        (fun x => solveWord (S.solve (systemAt q x))) (solveBound q.call q.witness)
        (fun x => solveCopyCost (S.solve (systemAt q x))) (systemList q) + 2 ≤
      solvedK B1 * (q.call.n + 1) ^ solvedE B1 B2 * solvedCost q solveBound := by
  have hout : ∀ x ∈ systemList q, (solveWord (S.solve (systemAt q x))).length ≤ (solveBound q.call q.witness) + 1 :=
    fun x hx => (output_length_le (solverOn S q) x).trans (by have := hB x hx; omega)
  have hitems := itemsCost_le (systemTag q) (fun x => sysWord (systemAt q x)) (solveBound q.call q.witness)
    (fun x => solveCopyCost (S.solve (systemAt q x))) (systemList q) (20000 * ((envelope q) * (envelope q) + ((q.call.n + 1) ^ sizeExp B1 B2) * ((q.call.n + 1) ^ sizeExp B1 B2) + ((q.call.n + 1) ^ sizeExp B1 B2) + 1) * ((solveBound q.call q.witness) + 1))
    (fun x hx => solvedItem_le S q (solveBound q.call q.witness) x (hout x hx))
  have hU := batchOut_length (RepairRepresentation.natWord q.call.n) (systemTag q)
    (fun x => solveWord (S.solve (systemAt q x))) (systemList q) (578 * ((envelope q) * (envelope q)) + 16 + (solveBound q.call q.witness) + 1) (fun x hx => by
      have h1 := systemTag_length_le q x
      have h2 := hout x hx
      have : 17 * (envelope q) * (17 * (envelope q)) = 289 * ((envelope q) * (envelope q)) := by ring
      omega)
  have hm := systemList_length_le q
  have hnw := natWord_length_le_self (systemList q).length
  have hnn := natWord_length_le_self q.call.n
  have hV : (envelope q) = (Cells.ParameterArithmetic.preparationCoefficient B1) * (q.call.n + 1) ^ (B1 + 12) := envelope_eq q
  have hVV : (envelope q) * (envelope q) ≤ (Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) := by
    rw [hV]
    calc (Cells.ParameterArithmetic.preparationCoefficient B1) * (q.call.n + 1) ^ (B1 + 12) * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (q.call.n + 1) ^ (B1 + 12)) =
        (Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * (q.call.n + 1) ^ (2 * (B1 + 12)) := by ring
      _ ≤ (Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hXX : ((q.call.n + 1) ^ sizeExp B1 B2) * ((q.call.n + 1) ^ sizeExp B1 B2) ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hX1 : 1 ≤ ((q.call.n + 1) ^ sizeExp B1 B2) := Nat.one_le_pow _ _ (by omega)
  have hXW : ((q.call.n + 1) ^ sizeExp B1 B2) ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) := le_trans (Nat.le_mul_self ((q.call.n + 1) ^ sizeExp B1 B2)) hXX
  have hW1 : 1 ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) := Nat.one_le_pow _ _ (by omega)
  have hQW : ((envelope q) * (envelope q) + ((q.call.n + 1) ^ sizeExp B1 B2) * ((q.call.n + 1) ^ sizeExp B1 B2) + ((q.call.n + 1) ^ sizeExp B1 B2) + 1) ≤ ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) := by nlinarith
  have hE : (q.call.n + 1) ^ solvedE B1 B2 = ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) := by
    rw [← pow_succ]; rfl
  have hT0e : solvedCost q solveBound = systemCount q * (rowCount q + (solveBound q.call q.witness) + 1) + (gammaWord q).length + 1 := rfl
  have hScB : systemCount q * ((solveBound q.call q.witness) + 1) ≤ solvedCost q solveBound := by
    rw [hT0e]; have := Nat.mul_le_mul_left (systemCount q) (show (solveBound q.call q.witness) + 1 ≤ rowCount q + (solveBound q.call q.witness) + 1 by omega); omega
  have hmB : (systemList q).length * ((solveBound q.call q.witness) + 1) ≤ systemCount q * ((solveBound q.call q.witness) + 1) := Nat.mul_le_mul_right _ hm
  have hI : (systemList q).length * (20000 * ((envelope q) * (envelope q) + ((q.call.n + 1) ^ sizeExp B1 B2) * ((q.call.n + 1) ^ sizeExp B1 B2) + ((q.call.n + 1) ^ sizeExp B1 B2) + 1) * ((solveBound q.call q.witness) + 1)) ≤
      20000 * (((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2))) * solvedCost q solveBound := by
    calc (systemList q).length * (20000 * ((envelope q) * (envelope q) + ((q.call.n + 1) ^ sizeExp B1 B2) * ((q.call.n + 1) ^ sizeExp B1 B2) + ((q.call.n + 1) ^ sizeExp B1 B2) + 1) * ((solveBound q.call q.witness) + 1)) = 20000 * ((envelope q) * (envelope q) + ((q.call.n + 1) ^ sizeExp B1 B2) * ((q.call.n + 1) ^ sizeExp B1 B2) + ((q.call.n + 1) ^ sizeExp B1 B2) + 1) * ((systemList q).length * ((solveBound q.call q.witness) + 1)) := by ring
      _ ≤ 20000 * (((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2))) * solvedCost q solveBound :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hQW) (hmB.trans hScB)
  have hUm : (systemList q).length * (578 * ((envelope q) * (envelope q)) + 16 + (solveBound q.call q.witness) + 1) ≤
      (578 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) + 17) * solvedCost q solveBound := by
    have hV3 : (envelope q) * (envelope q) ≤ ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) := by nlinarith
    have h1 : 578 * ((envelope q) * (envelope q)) + 16 + (solveBound q.call q.witness) + 1 ≤ (578 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) + 17) * ((solveBound q.call q.witness) + 1) := by nlinarith
    calc (systemList q).length * (578 * ((envelope q) * (envelope q)) + 16 + (solveBound q.call q.witness) + 1)
        ≤ (systemList q).length * ((578 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) + 17) * ((solveBound q.call q.witness) + 1)) := Nat.mul_le_mul_left _ h1
      _ = (578 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) + 17) * ((systemList q).length * ((solveBound q.call q.witness) + 1)) := by ring
      _ ≤ (578 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) + 17) * solvedCost q solveBound := Nat.mul_le_mul_left _ (hmB.trans hScB)
  have hT1 : 1 ≤ solvedCost q solveBound := by rw [hT0e]; omega
  have hmT : (systemList q).length ≤ solvedCost q solveBound :=
    le_trans (Nat.le_mul_of_pos_right _ (by omega)) (hmB.trans hScB)
  have hWT1 : 1 ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hnT : q.call.n + 1 ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) * solvedCost q solveBound := by
    calc q.call.n + 1 = (q.call.n + 1) * 1 := by ring
      _ ≤ (q.call.n + 1) * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound) := Nat.mul_le_mul_left _ hWT1
      _ = ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) * solvedCost q solveBound := by ring
  have hWT : ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) * solvedCost q solveBound := by
    calc ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound = ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound * 1 := by ring
      _ ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound * (q.call.n + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) * solvedCost q solveBound := by ring
  have hCW : (Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound) ≤ (Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) * solvedCost q solveBound) :=
    Nat.mul_le_mul_left _ hWT
  have hTW : solvedCost q solveBound ≤ ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound := Nat.le_mul_of_pos_left _ (by omega)
  unfold batchCost solvedK
  rw [hE]
  have e1 : 20000 * (((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2))) * solvedCost q solveBound =
      20000 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound)) + 60000 * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound) := by ring
  have e2 : (578 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * ((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) + 17) * solvedCost q solveBound =
      578 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound)) + 1734 * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * solvedCost q solveBound) +
        17 * solvedCost q solveBound := by ring
  have e3 : 1000000 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) + 3) * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1)) * solvedCost q solveBound =
      1000000 * ((Cells.ParameterArithmetic.preparationCoefficient B1) * (Cells.ParameterArithmetic.preparationCoefficient B1) * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) * solvedCost q solveBound)) +
        3000000 * (((q.call.n + 1) ^ (2 * (B1 + 12) + 2 * sizeExp B1 B2)) * (q.call.n + 1) * solvedCost q solveBound) := by ring
  rw [e3]
  rw [e1] at hI
  rw [e2] at hUm
  omega

/-! ## The stage -/

/-- **The stage `solved`** (`ReconstructPhases.solved`; Step 3, paper/paper.tex, with
`prop:time`): for every exact solver, the batch of its calls maps `systemsWord` to the framed
`solvedWord` within `solvedK (n+1)^{solvedE} solvedCost`. -/
noncomputable def solvedStage (B1 B2 : ℕ) : ∀ (S : SolveMachine) (solveBound : Call → List Bool → ℕ),
    (∀ (q : ChildRequest B1 B2) (s : SysReq), (sysWord s).length ≤ (q.call.n + 1) ^ sizeExp B1 B2 →
      S.budget s ≤ solveBound q.call q.witness) →
    WordFunction (ChildRequest B1 B2) systemsWord (fun q => frame (solvedWord q S))
      (fun q => solvedK B1 * (q.call.n + 1) ^ solvedE B1 B2 * solvedCost q solveBound) :=
  fun S solveBound hsolve =>
    NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal (batchP S.wf.program (solveCopier S.wf.program))
      (cOUT _) (by simp [cOUT]) (fun q => solvedCap q S (solveBound q.call q.witness)) (fun _ _ => 0)
      (fun q => batchCost (RepairRepresentation.natWord q.call.n) (systemTag q) (fun x => sysWord (systemAt q x))
        (fun x => solveWord (S.solve (systemAt q x))) (solveBound q.call q.witness)
        (fun x => solveCopyCost (S.solve (systemAt q x))) (systemList q))
      (fun q => solvedBatch_le S solveBound q (fun x _ => hsolve q _ (sysWord_le_sizeExp q x)))
      (fun q => ⟨rfl, solvedRun S solveBound hsolve q⟩)

end NearQuarticWires.Reconstruct.Batch
