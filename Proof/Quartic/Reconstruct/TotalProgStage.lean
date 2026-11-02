import Proof.Quartic.Reconstruct.TotalProgCost

/-!
# The sum of the answers within `K (n+1)^e` times its cost

Paper: `prop:time`, paper/paper.tex.

The run of the sum costs `O(U^4)` per number of its input, so with its input it costs at most `10^12 U^8` times
`solvedCost` (`totalRun_le`); the compiled budget is at most `totalK B₁ (n+1)^{totalE B₁} solvedCost`
(`totalBudget_le`). **`totalStage`** has the type of the field `ReconstructPhases.total`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.TotalProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats (SolveMachine solveWord SysReq sysWord)
open NearCubicGates.Close.Interfaces (Call)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct NearQuarticWires.Reconstruct.GatherProg
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

theorem sum_range_getD {α : Type} (L : List α) (d : α) (f : α → ℕ) :
    ∑ k ∈ Finset.range L.length, f (L.getD k d) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

theorem sum_map_affine {α : Type} (L : List α) (f : α → ℕ) (c k : ℕ) :
    (L.map fun d => c * (f d + k)).sum = c * ((L.map f).sum + k * L.length) := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

theorem length_le_flatMap_natWord (L : List ℕ) : L.length ≤ (L.flatMap natWord).length := by
  induction L with
  | nil => simp
  | cons v L ih => rw [List.flatMap_cons, List.length_append, natWord_length, List.length_cons]; omega

theorem ansLen_le (d : ItD) : ansLen d ≤ ((itN d).flatMap natWord).length := by
  refine le_trans ?_ (length_le_flatMap_natWord _)
  unfold ansLen itN
  cases d.ans with
  | none => simp
  | some L =>
    simp only [ansN, List.length_append, List.length_cons, List.length_nil]
    have := length_le_flatMap_natWord (L.flatMap entN)
    have h : L.length ≤ (L.flatMap entN).length := by
      induction L with
      | nil => simp
      | cons e L ih => simp [entN]; omega
    omega

theorem items_word_le (q : ChildRequest B1 B2) (S : SolveMachine) :
    ((itsQ q S).map fun d => ((itN d).flatMap natWord).length).sum ≤ (solvedWord q S).length := by
  rw [solvedWord_nats, List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append,
    List.flatMap_assoc, List.length_flatMap]
  omega

theorem bracket_le (V U E ℓ u A : ℕ) (hU : V + 1 ≤ U) (hE : E ≤ 9 * (V + 1) ^ 4)
    (hℓ : ℓ = 3 * (20000 * (V + 1) ^ 4) + 2 * E + 10) (hu : u = 30 * ℓ + 100) (hA : A = 10 ^ 5 * V ^ 4 + 4) :
    (3 * u + 50) * (A + 2) + 2 * u + emitShiftCost 0 ℓ + A + 31 ≤ 1000000000000 * U ^ 8 := by
  obtain ⟨X, hX⟩ : ∃ X, X = (V + 1) ^ 4 := ⟨_, rfl⟩
  rw [← hX] at hℓ hE
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_pow _ _ (by omega)
  have hV4 : V ^ 4 ≤ X := by rw [hX]; exact Nat.pow_le_pow_left (by omega) 4
  have hXU : X ≤ U ^ 4 := by rw [hX]; exact Nat.pow_le_pow_left hU 4
  have hℓ' : ℓ ≤ 60028 * X := by omega
  have hu' : 3 * u + 50 ≤ 5402950 * X := by omega
  have hA' : A + 2 ≤ 100006 * X := by omega
  have hp : (3 * u + 50) * (A + 2) ≤ (5402950 * X) * (100006 * X) := Nat.mul_le_mul hu' hA'
  have he : emitShiftCost 0 ℓ ≤ 2881500 * X := by
    have : emitShiftCost 0 ℓ = 48 * ℓ + 156 := by unfold emitShiftCost emitNatDCost; norm_num; ring
    omega
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left _ hX1
  have hX2 : X * X ≤ U ^ 8 := by
    calc X * X ≤ U ^ 4 * U ^ 4 := Nat.mul_le_mul hXU hXU
      _ = U ^ 8 := by ring
  have e1 : (5402950 * X) * (100006 * X) = 540327417700 * (X * X) := by ring
  omega

/-- **The run of the sum and its input cost at most `10^12 U^8` times the solved cost.** -/
theorem totalRun_le (q : ChildRequest B1 B2) (S : SolveMachine) (solveBound : Call → List Bool → ℕ) (U : ℕ)
    (hU : envelope q + 1 ≤ U) :
    totalCost (ellT q) (itsQ q S) + (solvedWord q S).length + 1 ≤
      1000000000000 * U ^ 8 * solvedCost q solveBound := by
  set ℓ := ellT q with hℓ
  set u := unitC ℓ with hu
  set A := 10 ^ 5 * envelope q ^ 4 + 4 with hA
  set S0 := systemCount q + (gammaWord q).length + 1 with hS0
  have hW0 : (solvedWord q S).length ≤ A * S0 := solvedWord_length_le S q
  have hm : (itsQ q S).length ≤ S0 := by
    have := systemList_length_le q; simp only [itsQ, List.length_map]; omega
  have hitems := items_word_le q S
  -- the items
  have hsum : ((itsQ q S).map fun d => itCost ℓ d + 2).sum ≤
      (3 * u + 50) * (((itsQ q S).map fun d => ((itN d).flatMap natWord).length).sum + 2 * (itsQ q S).length) := by
    have h1 : ∀ d, itCost ℓ d + 2 ≤ (3 * u + 50) * (((itN d).flatMap natWord).length + 2) := by
      intro d
      have := ansLen_le d
      have := Nat.mul_le_mul_left (3 * u + 14) this
      unfold itCost; rw [← hu]; nlinarith
    calc ((itsQ q S).map fun d => itCost ℓ d + 2).sum
        ≤ ((itsQ q S).map fun d => (3 * u + 50) * (((itN d).flatMap natWord).length + 2)).sum :=
          List.sum_le_sum (fun d _ => h1 d)
      _ = (3 * u + 50) * (((itsQ q S).map fun d => ((itN d).flatMap natWord).length).sum +
            2 * (itsQ q S).length) := by
          exact sum_map_affine _ _ _ _
  have hcost : totalCost ℓ (itsQ q S) = ((itsQ q S).map fun d => itCost ℓ d + 2).sum + 2 * u +
      emitShiftCost 0 ℓ + 30 := by
    unfold totalCost; rw [sum_range_getD (itsQ q S) d0 (fun d => itCost ℓ d + 2)]
  have hS0b : S0 ≤ solvedCost q solveBound := by
    unfold solvedCost
    have := Nat.le_mul_of_pos_right (systemCount q) (show 0 < rowCount q + solveBound q.call q.witness + 1 by omega)
    omega
  have hEx : emitExp q ≤ 9 * (envelope q + 1) ^ 4 := by
    unfold emitExp
    have : envelope q * (envelope q + 2) ≤ (envelope q + 1) ^ 2 := by nlinarith
    have : (envelope q + 1) ^ 2 ≤ (envelope q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : 1 ≤ (envelope q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hB := bracket_le (envelope q) U (emitExp q) ℓ u A hU hEx rfl rfl rfl
  have hS01 : 1 ≤ S0 := by omega
  -- the total
  have k1 : (3 * u + 50) * (((itsQ q S).map fun d => ((itN d).flatMap natWord).length).sum + 2 * (itsQ q S).length) ≤
      (3 * u + 50) * ((A + 2) * S0) := Nat.mul_le_mul_left _ (by nlinarith)
  have k2 : 2 * u + emitShiftCost 0 ℓ + 30 + (solvedWord q S).length + 1 ≤
      (2 * u + emitShiftCost 0 ℓ + A + 31) * S0 := by nlinarith
  have k3 : (3 * u + 50) * ((A + 2) * S0) + (2 * u + emitShiftCost 0 ℓ + A + 31) * S0 =
      ((3 * u + 50) * (A + 2) + 2 * u + emitShiftCost 0 ℓ + A + 31) * S0 := by ring
  have k4 : ((3 * u + 50) * (A + 2) + 2 * u + emitShiftCost 0 ℓ + A + 31) * S0 ≤
      1000000000000 * U ^ 8 * solvedCost q solveBound := Nat.mul_le_mul hB hS0b
  rw [hcost]
  omega

/-- The constant of the sum stage. -/
noncomputable def totalK (B1 : ℕ) : ℕ :=
  10000000000000000 * (201 + emitTapes) ^ 2 * ((emitSizes B1).a1 * 2 ^ (emitSizes B1).c1) ^ 10

/-- The exponent of the sum stage. -/
def totalE (B1 : ℕ) : ℕ := 10 * (emitSizes B1).c1

theorem scaleU_pow10 (q : ChildRequest B1 B2) :
    scaleU B1 q ^ 10 = ((emitSizes B1).a1 * 2 ^ (emitSizes B1).c1) ^ 10 * (q.call.n + 1) ^ totalE B1 := by
  unfold scaleU totalE
  rw [mul_pow, ← pow_mul, mul_comm (emitSizes B1).c1 10]

/-- **The budget of the sum stage.** -/
theorem totalBudget_le (S : SolveMachine) (solveBound : Call → List Bool → ℕ) (q : ChildRequest B1 B2) :
    totalBudget B1 S q ≤ totalK B1 * (q.call.n + 1) ^ totalE B1 * solvedCost q solveBound := by
  obtain ⟨ha, hc, hn, h128⟩ := scaleU_facts q
  have hWU : (emitSizes B1).W (leadOnes (solvedWord q S)) ≤ scaleU B1 q := by
    rw [leadOnes_solvedWord, ← leadOnes_gatheredWord]; exact width_le_U q
  have hVU := envelope_le_U q
  have hN := totalRun_le q S solveBound (scaleU B1 q) hVU
  set U := scaleU B1 q with hU
  set T := emitTapes with hT
  set S' := U + 200 + T with hS
  have hL : leadOnes (solvedWord q S) ≤ S' := by
    rw [leadOnes_solvedWord]; have := natBitLength_le_succ' q.call.n; omega
  have hlang := NearQuarticWires.StageMain.Runtime.langBudget_le
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) VV MM (solvedWord q S)
    (totalCost (ellT q) (itsQ q S)) S'
    (by omega) (show (128 : ℕ) ≤ S' by omega) (show (10 : ℕ) ≤ S' by omega) (show T ≤ S' by omega) (by omega)
    (by omega) (by simp [emitSizes]) (by simp [emitSizes]) (by simp [emitSizes]) (by simp [emitSizes]) hL (by omega)
    (by simp [Sz.Lk, emitSizes]) (by simp [Sz.Bk, emitSizes])
  have hSU : S' ≤ (201 + T) * U := by nlinarith
  have hS2 : S' ^ 2 ≤ (201 + T) ^ 2 * U ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hSU 2
  calc totalBudget B1 S q ≤ 10000 * S' ^ 2 * (totalCost (ellT q) (itsQ q S) + (solvedWord q S).length + 1) := hlang
    _ ≤ 10000 * ((201 + T) ^ 2 * U ^ 2) * (1000000000000 * U ^ 8 * solvedCost q solveBound) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hS2) hN
    _ = 10000000000000000 * (201 + T) ^ 2 * U ^ 10 * solvedCost q solveBound := by ring
    _ = totalK B1 * (q.call.n + 1) ^ totalE B1 * solvedCost q solveBound := by
        rw [scaleU_pow10]; unfold totalK; ring

/-- **The sum stage** `solvedWord ↦ intWord Ψ̃(π)` within `totalK B₁ (n+1)^{totalE B₁} solvedCost`: the type of the
field `ReconstructPhases.total` with these constants. -/
noncomputable def totalStage (B1 B2 : ℕ) : ∀ (solver : SolveMachine) (solveBound : Call → List Bool → ℕ),
    (∀ (q : ChildRequest B1 B2) (s : SysReq), (sysWord s).length ≤ (q.call.n + 1) ^ sizeExp B1 B2 →
      solver.budget s ≤ solveBound q.call q.witness) →
    WordFunction (ChildRequest B1 B2) (fun q => solvedWord q solver)
      (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q))
      (fun q => totalK B1 * (q.call.n + 1) ^ totalE B1 * solvedCost q solveBound) :=
  fun S solveBound _ => WordFunction.enlargeBudget (totalWF B1 B2 S) (totalBudget_le S solveBound)

end NearQuarticWires.Reconstruct.TotalProg
