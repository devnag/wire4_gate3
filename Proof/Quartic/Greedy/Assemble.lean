import Proof.Quartic.Greedy.Ledger
import Proof.Quartic.Greedy.Solve
import Proof.Quartic.Cells.ParametersWordBounds

/-!
# One child evaluation from its subroutines, with its cost

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

`SubroutineCosts` collects the three subroutines of a child evaluation with the costs that `prop:time` assigns to
them: one coefficient in `(Q+1)^{2m} poly(n)` time, one table of recovered counts in `2^{n-k} poly(n)`
time (`lem:print`(a), `lem:residue`), and one exact system in time polynomial in its size. From
the controls of the two stages (`GammaTableControl`, `ReconstructControl`), `childComponents` builds the components
of a child evaluation, and proves that their cost is a ledger cost (`childComponents_cost`): this is the Step 3 part
of `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- `prop:time`: the word after parameter preparation (the call, the §9 parameters and the witness
prefix) has polynomial length in the call word. -/
def PrepSize (B1 B2 : ℕ) : Prop := PolyCost fun c w => (prepWord B1 B2 c w).length

/-- The length of the word after parameter preparation is bounded by the cost of any word function writing it; in
particular the `prep` stage of `Program.MachineComponents` gives `PrepSize`. -/
theorem prepSize_of_prep {prepBudget : Call → List Bool → ℕ}
    (prep : WordFunction (Call × List Bool) requestWord (fun r => frame (prepWord B1 B2 r.1 r.2))
      (fun r => prepBudget r.1 r.2))
    (hcost : PolyCost prepBudget) : PrepSize B1 B2 := by
  obtain ⟨K, e, h⟩ := hcost
  refine ⟨K + 1, e, fun c w => ?_⟩
  have h1 := NearCubicGates.Close.Cells.wf_out_len prep (c, w)
  rw [frame_length] at h1
  have h2 := h c w
  have h3 : 1 ≤ ((callWord c).length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  dsimp only at h1 ⊢
  nlinarith

theorem flatMap_length_le {α : Type} (f : α → List Bool) (B : ℕ) :
    ∀ xs : List α, (∀ x ∈ xs, (f x).length ≤ B) → (xs.flatMap f).length ≤ xs.length * B
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := flatMap_length_le f B l (fun x hx => h x (by simp [hx]))
    nlinarith

/-- **The subroutines of a child evaluation with their costs** (`prop:time`, paper/paper.tex). -/
structure SubroutineCosts (B1 B2 : ℕ) where
  /-- The cost of one coefficient. -/
  gammaBudget : Machine.GammaRequest → ℕ
  /-- One coefficient `2^S c_π(w)` (`cor:conditional`; the type of `Machine.GammaProgramObligation`). -/
  gamma : WordFunction Machine.GammaRequest Machine.gammaRequestWord
    (fun r => NearCubicGates.Close.Interfaces.intWord (Machine.gammaTarget r)) gammaBudget
  /-- The constant of the cost of one coefficient. -/
  Kγ : ℕ
  /-- The exponent of the cost of one coefficient. -/
  eγ : ℕ
  /-- One coefficient costs `(Q+1)^{2m} poly(n)` (`prop:time`). -/
  gammaCost : ∀ (q : ChildRequest B1 B2) (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder),
    gammaBudget (gammaRequest q w) ≤ Kγ * (q.selected.1.Q + 1) ^ (2 * Algorithm.traceOrder) * (q.call.n + 1) ^ eγ
  /-- The cost of one table. -/
  printBudget : PrintRequest B1 B2 → ℕ
  /-- One table of recovered counts `z ↦ 𝒩(z)` (`lem:print`(a), `lem:residue`). -/
  print : WordFunction (PrintRequest B1 B2) printInput
    (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) printBudget
  /-- The constant of the cost of one table. -/
  Kp : ℕ
  /-- The exponent of the cost of one table. -/
  ep : ℕ
  /-- One printed table costs `2^{n-k} poly(n)` (`lem:print`), plus a polynomial in the size of its
  indices. -/
  printCost : ∀ r : PrintRequest B1 B2,
    printBudget r ≤ Kp * (2 ^ (r.child.call.n - r.child.selected.1.k) * (r.child.call.n + 1) ^ ep +
      ((printIndexWord r).length + 1) ^ ep)
  /-- The exact solver (for instance `NearCubicGates.Close.Solve.solveMachine`). -/
  solver : Formats.SolveMachine

namespace SubroutineCosts

variable (Sub : SubroutineCosts B1 B2)

/-- The constant of the polynomial cost of the exact solver. -/
noncomputable def solveK : ℕ := Classical.choose Sub.solver.cls

/-- The exponent of the polynomial cost of the exact solver. -/
noncomputable def solveE : ℕ := Classical.choose (Classical.choose_spec Sub.solver.cls)

theorem solve_cls (s : Formats.SysReq) :
    Sub.solver.budget s ≤ Sub.solveK * ((Formats.sysWord s).length + 1) ^ Sub.solveE :=
  Classical.choose_spec (Classical.choose_spec Sub.solver.cls) s

/-- The cost of one coefficient on a call. -/
noncomputable def gammaBound (c : Call) (_w : List Bool) : ℕ :=
  match dispatch B1 B2 c with
  | some p => Sub.Kγ * (p.1.Q + 1) ^ (2 * Algorithm.traceOrder) * (c.n + 1) ^ Sub.eγ
  | none => 0

/-- The cost of one printed table with indices of size at most `(n+1)^{e₀}` on a call. -/
noncomputable def printBound (e₀ : ℕ) (c : Call) (_w : List Bool) : ℕ :=
  match dispatch B1 B2 c with
  | some p => Sub.Kp * (2 ^ (c.n - p.1.k) * (c.n + 1) ^ Sub.ep + ((c.n + 1) ^ e₀ + 1) ^ Sub.ep)
  | none => 0

/-- The cost of one exact system of size at most `(n+1)^{e₀}`. -/
noncomputable def solveBound (e₀ : ℕ) (c : Call) (_w : List Bool) : ℕ :=
  Sub.solveK * ((c.n + 1) ^ e₀ + 1) ^ Sub.solveE

theorem gammaBound_spec (q : ChildRequest B1 B2) (w : Cycle.Walk q.cellCall.seed.N Algorithm.traceOrder) :
    Sub.gammaBudget (gammaRequest q w) ≤ Sub.gammaBound q.call q.witness := by
  unfold gammaBound
  rw [q.dispatched]
  exact Sub.gammaCost q w

theorem printBound_spec (e₀ : ℕ) (r : PrintRequest B1 B2)
    (h : (printIndexWord r).length ≤ (r.child.call.n + 1) ^ e₀) :
    Sub.printBudget r ≤ Sub.printBound e₀ r.child.call r.child.witness := by
  unfold printBound
  rw [r.child.dispatched]
  refine (Sub.printCost r).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _))
  exact Nat.pow_le_pow_left (by omega) _

theorem solveBound_spec (e₀ : ℕ) (q : ChildRequest B1 B2) (s : Formats.SysReq)
    (h : (Formats.sysWord s).length ≤ (q.call.n + 1) ^ e₀) :
    Sub.solver.budget s ≤ Sub.solveBound e₀ q.call q.witness :=
  (Sub.solve_cls s).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

/-- The coefficient stage from its control and one coefficient. -/
noncomputable def gammaStage (GT : GammaTableControl B1 B2) :=
  GT.program Sub.gammaBudget Sub.gammaBound Sub.gamma Sub.gammaBound_spec

/-- The reconstruction stage from its control, one table and the exact solver. -/
noncomputable def reconstructStage (RC : ReconstructControl B1 B2) :=
  RC.program Sub.printBudget Sub.solver (Sub.printBound RC.e₀) (Sub.solveBound RC.e₀) Sub.print
    (Sub.printBound_spec RC.e₀) (Sub.solveBound_spec RC.e₀)

/-- The bound on the cost of the coefficient stage at the parameters `p` of a dispatched call. -/
noncomputable def gammaStageBound (GT : GammaTableControl B1 B2) (c : Call) (p : Selected c) (w : List Bool) : ℕ :=
  GT.K * ((p.1.N ^ (2 * Algorithm.traceOrder) + 1) *
    (Sub.Kγ * (p.1.Q + 1) ^ (2 * Algorithm.traceOrder) * (c.n + 1) ^ Sub.eγ + (c.n + 1) ^ GT.e + p.1.S) +
    ((certWord B1 B2 c w).length + 2 * p.1.S + 1) + 1)

/-- The bound on the cost of the reconstruction stage at the parameters `p` of a dispatched call. -/
noncomputable def reconstructStageBound (GT : GammaTableControl B1 B2) (RC : ReconstructControl B1 B2) (c : Call)
    (p : Selected c) (w : List Bool) : ℕ :=
  RC.K * (c.n + 1) ^ RC.e *
    (2 * 4 ^ Algorithm.traceOrder * p.1.P ^ (2 * (p.1.J - 1 + 1) + 3) *
        (Sub.Kp * (2 ^ (c.n - p.1.k) * (c.n + 1) ^ Sub.ep + ((c.n + 1) ^ RC.e₀ + 1) ^ Sub.ep) +
          (prepWord B1 B2 c w).length +
          (2 * (8 * p.1.k + 3 + p.1.N ^ (2 * Algorithm.traceOrder) *
            (Sub.Kγ * (p.1.Q + 1) ^ (2 * Algorithm.traceOrder) * (c.n + 1) ^ Sub.eγ + 1)) + 1) +
          2 ^ (c.n - p.1.k) + (c.n + 1) ^ RC.e₀) +
      2 * 2 ^ (c.n - p.1.k) * 4 ^ Algorithm.traceOrder * p.1.P ^ (2 * (p.1.J - 1 + 1)) *
        (p.1.P ^ 3 + Sub.solveK * ((c.n + 1) ^ RC.e₀ + 1) ^ Sub.solveE + 1) +
      Sub.gammaStageBound GT c p w + 1)

/-- The bound on the cost of a child evaluation of a call: the sum of the two stage bounds on a dispatched call. -/
noncomputable def stageBound (GT : GammaTableControl B1 B2) (RC : ReconstructControl B1 B2) (c : Call)
    (w : List Bool) : ℕ :=
  match dispatch B1 B2 c with
  | some p => Sub.gammaStageBound GT c p w + Sub.reconstructStageBound GT RC c p w
  | none => 0

end SubroutineCosts

namespace SubroutineCosts

variable (Sub : SubroutineCosts B1 B2) (GT : GammaTableControl B1 B2) (RC : ReconstructControl B1 B2)

/-- The cost of the coefficient stage of a child is at most `gammaStageBound` at the parameters of its call. -/
theorem gammaStage_budget_le (q : ChildRequest B1 B2) :
    GT.K * ((q.cellCall.seed.N ^ (2 * Algorithm.traceOrder) + 1) *
        (Sub.gammaBound q.call q.witness + (q.call.n + 1) ^ GT.e + q.seedPrefix.length) + (childInput q).length + 1)
      ≤ Sub.gammaStageBound GT q.call q.selected q.witness := by
  have hN : q.cellCall.seed.N = q.selected.1.N :=
    Cells.ParameterRules.seed_N (Cells.prepare_spec _ q.selected.1 q.selected.2)
  have hγ : Sub.gammaBound q.call q.witness =
      Sub.Kγ * (q.selected.1.Q + 1) ^ (2 * Algorithm.traceOrder) * (q.call.n + 1) ^ Sub.eγ := by
    unfold gammaBound
    rw [q.dispatched]
  have hπ : q.seedPrefix.length ≤ q.selected.1.S := q.prefix_le.trans (seedLength_runCall q.selected q.witness).le
  have hin : (childInput q).length = (certWord B1 B2 q.call q.witness).length + 2 * q.seedPrefix.length + 1 := by
    unfold childInput
    rw [List.length_append, frame_length]
    ring
  unfold gammaStageBound
  rw [hN, hγ, hin]
  gcongr

/-- The framed coefficient table of a child has at most `2^{4k}` entries, each of length at most the cost of one
coefficient plus one. -/
theorem gammaTableWord_length_le (q : ChildRequest B1 B2) :
    (gammaTableWord q).length ≤ 2 * (8 * q.selected.1.k + 3 + q.selected.1.N ^ (2 * Algorithm.traceOrder) *
      (Sub.Kγ * (q.selected.1.Q + 1) ^ (2 * Algorithm.traceOrder) * (q.call.n + 1) ^ Sub.eγ + 1)) + 1 := by
  have hs := Cells.prepare_spec _ q.selected.1 q.selected.2
  have hN : q.cellCall.seed.N = q.selected.1.N := Cells.ParameterRules.seed_N hs
  have hN8 : q.selected.1.N ^ (2 * Algorithm.traceOrder) ≤ 2 ^ (4 * q.selected.1.k) := by
    show q.selected.1.N ^ 8 ≤ _
    rw [hs.N_eq, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlen : (gammaTable q).length = q.selected.1.N ^ (2 * Algorithm.traceOrder) := by
    unfold gammaTable
    rw [List.length_map, walkList_length, hN]
  have hnat : (natWord (gammaTable q).length).length ≤ 2 * (4 * q.selected.1.k) + 3 := by
    rw [hlen]
    exact Cells.ParameterArithmetic.natWord_length_of_power_bound _ _ hN8
  have hentry : ∀ x ∈ gammaTable q, (NearCubicGates.Close.Interfaces.intWord x).length ≤
      Sub.Kγ * (q.selected.1.Q + 1) ^ (2 * Algorithm.traceOrder) * (q.call.n + 1) ^ Sub.eγ + 1 := by
    intro x hx
    unfold gammaTable at hx
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
    have h1 := NearCubicGates.Close.Cells.wf_out_len Sub.gamma (gammaRequest q w)
    have h2 := Sub.gammaCost q w
    rw [gammaTarget_gammaRequest] at h1
    omega
  have hflat := flatMap_length_le NearCubicGates.Close.Interfaces.intWord _ (gammaTable q) hentry
  rw [hlen] at hflat
  unfold gammaTableWord listWord
  rw [frame_length, List.length_append]
  nlinarith

/-- The cost of the reconstruction stage of a child is at most `reconstructStageBound` at the parameters of its
call. -/
theorem reconstructStage_budget_le (q : ChildRequest B1 B2)
    (hgw : (gammaWord q).length ≤ Sub.gammaStageBound GT q.call q.selected q.witness) :
    RC.K * (q.call.n + 1) ^ RC.e *
        (tableCount q * (Sub.printBound RC.e₀ q.call q.witness + (prepWord B1 B2 q.call q.witness).length +
            (gammaTableWord q).length + q.cellCall.ncol + (q.call.n + 1) ^ RC.e₀) +
          systemCount q * (rowCount q + Sub.solveBound RC.e₀ q.call q.witness + 1) +
          (gammaWord q).length + 1)
      ≤ Sub.reconstructStageBound GT RC q.call q.selected q.witness := by
  have hp : Sub.printBound RC.e₀ q.call q.witness = Sub.Kp * (2 ^ (q.call.n - q.selected.1.k) *
      (q.call.n + 1) ^ Sub.ep + ((q.call.n + 1) ^ RC.e₀ + 1) ^ Sub.ep) := by
    unfold printBound
    rw [q.dispatched]
  have hJ : q.cellCall.J = q.selected.1.J - 1 := rfl
  have hcol : q.cellCall.ncol = 2 ^ (q.call.n - q.selected.1.k) := rfl
  have hg := Sub.gammaTableWord_length_le q
  unfold reconstructStageBound tableCount systemCount rowCount solveBound
  rw [hp, hJ, hcol]
  gcongr

/-- **The cost of a child evaluation is a ledger cost** (`prop:time`). -/
theorem stageBound_cost (hC : CertSize B1 B2) (hP : PrepSize B1 B2) : LedgerCost B1 B2 (Sub.stageBound GT RC) := by
  obtain ⟨Kpp, epp, hpp⟩ := hP
  obtain ⟨Cc, dc, hCc⟩ := callWord_pow_le (B1 := B1) (B2 := B2) epp
  obtain ⟨A, d, E, hA⟩ := childArith GT.K GT.e Sub.Kγ Sub.eγ Sub.Kp Sub.ep Sub.solveK Sub.solveE
    RC.e₀ RC.K RC.e (8 * (2 * B1 + 100)) (8 * (2 * B1 + 103)) (Kpp * Cc) dc
  -- the bound, with the polynomial factor only on dispatched calls
  let f : Call → List Bool → ℕ := fun c _ =>
    match dispatch B1 B2 c with
    | some _ => A * (c.n + 1) ^ d
    | none => 0
  have hf : LedgerCost B1 B2 fun c w => f c w * ((certWord B1 B2 c w).length + 1) := by
    refine LedgerCost.mul_dispatched A d (fun c w h => ?_) (fun c w p h => ?_) ?_
    · simp only [f, h]
      exact Nat.zero_le _
    · simp only [f, h]
      exact le_rfl
    · exact LedgerCost.add hC (LedgerCost.of_poly ⟨1, 0, fun _ _ => by simp⟩)
  have hR : LedgerCost B1 B2 fun c (_ : List Bool) => A * runEnvelope B1 B2 E c :=
    ⟨A, E, fun c w => Nat.le_add_left _ _⟩
  refine LedgerCost.mono (fun c w => ?_) (LedgerCost.add hf hR)
  unfold stageBound
  split
  · rename_i p hp
    have hs := Cells.prepare_spec _ p.1 p.2
    have hadm := (dispatch_admitted hp).1
    have hn : 4 ≤ c.n := hadm.1
    have hlam : c.n ≤ 2 ^ p.1.lambda := by
      rw [hs.lambda_eq]
      exact Nat.le_pow_clog (by norm_num) _
    have hN : p.1.N ^ 8 ≤ 2 ^ (4 * p.1.k) := by
      rw [hs.N_eq, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb : 1 ≤ (Builder.callInput c).beta * ((Builder.callInput c).n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
    have hQe := Cells.ParameterRules.Qexp_upper hs B1 hb
    have hQ : (p.1.Q + 1) ^ 8 ≤ 2 ^ 8 * 2 ^ (6 * p.1.k + 8 * (2 * B1 + 100) * p.1.lambda) := by
      rw [hs.Q_eq]
      have h1 : 2 ^ p.1.Qexp + 1 ≤ 2 ^ (p.1.Qexp + 1) := by
        rw [pow_succ]
        have : 1 ≤ 2 ^ p.1.Qexp := Nat.one_le_two_pow
        omega
      calc (2 ^ p.1.Qexp + 1) ^ 8 ≤ (2 ^ (p.1.Qexp + 1)) ^ 8 := Nat.pow_le_pow_left h1 8
        _ = 2 ^ 8 * 2 ^ (8 * p.1.Qexp) := by rw [← pow_mul, ← pow_add]; congr 1; ring
        _ ≤ 2 ^ 8 * 2 ^ (6 * p.1.k + 8 * (2 * B1 + 100) * p.1.lambda) := by
            apply Nat.mul_le_mul_left
            apply Nat.pow_le_pow_right (by norm_num)
            have h3 : 8 * (3 * p.1.k / 4) ≤ 6 * p.1.k := by omega
            nlinarith
    have hPn : p.1.P ≤ c.n := (Cells.ParameterRules.prime_maximal hs).2.1
    have hk : p.1.k ≤ c.n := (Cells.ParameterRules.k_lt_n hs).le
    have hk10 : 10 * p.1.k ≤ c.n - p.1.k := by
      have hd := hs.initial_degree
      unfold Cells.ParameterArithmetic.DegreePass at hd
      rw [hs.m_eq] at hd
      change 100 * (4 * p.1.k + 2 + 0 * Nat.clog 2 p.1.Uocc) ≤ c.n - p.1.k at hd
      omega
    have hlam2 : 2 ^ p.1.lambda ≤ 2 * c.n := by
      rw [hs.lambda_eq]
      have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < (Builder.callInput c).n by
        change 1 < c.n
        omega)
      have h2 : 1 ≤ Nat.clog 2 (Builder.callInput c).n := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by
        change 1 < c.n
        omega))
      change 2 ^ Nat.clog 2 (Builder.callInput c).n ≤ 2 * (Builder.callInput c).n
      rw [Nat.pred_eq_sub_one] at h1
      have h3 : 2 ^ Nat.clog 2 (Builder.callInput c).n = 2 * 2 ^ (Nat.clog 2 (Builder.callInput c).n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3]
      omega
    have hLp : (prepWord B1 B2 c w).length ≤ Kpp * Cc * (c.n + 1) ^ dc := by
      calc (prepWord B1 B2 c w).length ≤ Kpp * ((callWord c).length + 1) ^ epp := hpp c w
        _ ≤ Kpp * (Cc * (c.n + 1) ^ dc) := Nat.mul_le_mul_left _ (hCc c hadm)
        _ = Kpp * Cc * (c.n + 1) ^ dc := by ring
    have hJ : p.1.J - 1 + 1 ≤ p.1.Jmax + 1 := by have := hs.J_bound; omega
    have hS : p.1.S ≤ 8 * (2 * B1 + 103) * (c.n + 1) := by
      have h := seedRounds_le (B1 := B1) (B2 := B2) c
      unfold seedRounds at h
      rw [hp] at h
      exact h
    have key := hA c.n p.1.k p.1.N p.1.Q p.1.S p.1.P p.1.J p.1.Jmax p.1.lambda (certWord B1 B2 c w).length
      (prepWord B1 B2 c w).length
      (2 * (8 * p.1.k + 3 + p.1.N ^ 8 * (Sub.Kγ * (p.1.Q + 1) ^ 8 * (c.n + 1) ^ Sub.eγ + 1)) + 1)
      (by omega) hlam hN hQ hPn hJ hS hk hk10 hlam2 hLp le_rfl
    have henv : runEnvelope B1 B2 E c = Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda E := by
      unfold runEnvelope
      rw [hp]
    simp only [f, hp, henv]
    unfold gammaStageBound reconstructStageBound
    have e8 : 2 * Algorithm.traceOrder = 8 := rfl
    have e4 : (4 : ℕ) ^ Algorithm.traceOrder = 4 ^ 4 := rfl
    rw [e8, e4]
    exact key
  · exact Nat.zero_le _

/-- **One child evaluation from its subroutines** (Step 3, paper/paper.tex, with `prop:time`): the
coefficient stage and the reconstruction stage from their controls and the three subroutines, with a cost bound that
is a ledger cost. -/
noncomputable def childComponents (hC : CertSize B1 B2) (hP : PrepSize B1 B2) : ChildComponents B1 B2 where
  gammaBudget := fun q => GT.K * ((q.cellCall.seed.N ^ (2 * Algorithm.traceOrder) + 1) *
    (Sub.gammaBound q.call q.witness + (q.call.n + 1) ^ GT.e + q.seedPrefix.length) + (childInput q).length + 1)
  gammaStage := Sub.gammaStage GT
  reconstructBudget := fun q => RC.K * (q.call.n + 1) ^ RC.e *
    (tableCount q * (Sub.printBound RC.e₀ q.call q.witness + (prepWord B1 B2 q.call q.witness).length +
        (gammaTableWord q).length + q.cellCall.ncol + (q.call.n + 1) ^ RC.e₀) +
      systemCount q * (rowCount q + Sub.solveBound RC.e₀ q.call q.witness + 1) +
      (gammaWord q).length + 1)
  reconstructStage := Sub.reconstructStage RC
  childBound := Sub.stageBound GT RC
  bound_spec := fun q => by
    have h1 := Sub.gammaStage_budget_le GT q
    have hgw : (gammaWord q).length ≤ Sub.gammaStageBound GT q.call q.selected q.witness := by
      have h := NearCubicGates.Close.Cells.wf_out_len (Sub.gammaStage GT) q
      rw [frame_length] at h
      omega
    have h2 := Sub.reconstructStage_budget_le GT RC q hgw
    unfold stageBound
    rw [q.dispatched]
    exact Nat.add_le_add h1 h2
  childCost := Sub.stageBound_cost GT RC hC hP

end SubroutineCosts

/-- **The `greedy` field from the controls and the subroutines** (Step 3, paper/paper.tex, with
`prop:time`): from the control of the `S` rounds, the controls of the two stages of a child, the three subroutines
with their costs, and the `prep` and `cert` stages (for the lengths of `prepWord` and `certWord`), a word function
from `certWord` to `frame greedyWord` whose cost is a ledger cost. -/
theorem greedy_of_subroutines (loop : SeedLoop B1 B2) (GT : GammaTableControl B1 B2) (RC : ReconstructControl B1 B2)
    (Sub : SubroutineCosts B1 B2) {prepBudget : Call → List Bool → ℕ}
    (prep : WordFunction (Call × List Bool) requestWord (fun r => frame (prepWord B1 B2 r.1 r.2))
      (fun r => prepBudget r.1 r.2))
    (hprep : PolyCost prepBudget) {certBudget : Call → List Bool → ℕ}
    (cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
      (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2))
    (hcost : LedgerCost B1 B2 certBudget) :
    ∃ greedyBudget : Call → List Bool → ℕ,
      Nonempty (WordFunction (Call × List Bool) (fun r => certWord B1 B2 r.1 r.2)
        (fun r => frame (greedyWord B1 B2 r.1 r.2)) (fun r => greedyBudget r.1 r.2)) ∧
      LedgerCost B1 B2 greedyBudget :=
  greedy_of_child loop (Sub.childComponents GT RC (certSize_of_cert cert hcost) (prepSize_of_prep prep hprep)) cert
    hcost

/-- **The parts of the `greedy` stage** (Step 3, `sec:algorithm`, paper/paper.tex): the control of the `S` rounds,
the controls of the two stages of a child evaluation, and the three subroutines with their costs. -/
structure GreedyParts (B1 B2 : ℕ) where
  /-- The control of the `S` rounds. -/
  loop : SeedLoop B1 B2
  /-- The control of the coefficient stage. -/
  gammaTable : GammaTableControl B1 B2
  /-- The control of the reconstruction stage. -/
  reconstruct : ReconstructControl B1 B2
  /-- One coefficient, one table of recovered counts and the exact solver, with their costs. -/
  subroutines : SubroutineCosts B1 B2

/-- **The machine components of the counter with the `greedy` stage assembled from its parts**
(`sec:algorithm`, paper/paper.tex, with `prop:time`): the stages `prep`, `cert`, `main` and
`output` with their costs, and the parts of `greedy`. The lengths of `prepWord` and `certWord` needed for the cost of
`greedy` are read off the `prep` and `cert` stages. -/
noncomputable def machineComponentsOfParts (prepBudget : Call → List Bool → ℕ)
    (prep : WordFunction (Call × List Bool) requestWord (fun r => frame (prepWord B1 B2 r.1 r.2))
      (fun r => prepBudget r.1 r.2))
    (prepCost : PolyCost prepBudget) (certBudget : Call → List Bool → ℕ)
    (cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
      (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2))
    (certCost : LedgerCost B1 B2 certBudget) (G : GreedyParts B1 B2) (mainBudget : Call → List Bool → ℕ)
    (main : WordFunction (Call × List Bool) (fun r => greedyWord B1 B2 r.1 r.2)
      (fun r => frame (mainWord B1 B2 r.1 r.2)) (fun r => mainBudget r.1 r.2))
    (mainCost : LedgerCost B1 B2 mainBudget) (outputBudget : Call → List Bool → ℕ)
    (output : WordFunction (Call × List Bool) (fun r => mainWord B1 B2 r.1 r.2)
      (fun r => outputWord (admittedValue B1 B2 Builder.value r.1 r.2)) (fun r => outputBudget r.1 r.2))
    (outputCost : PolyCost outputBudget) : MachineComponents B1 B2 :=
  let hC := certSize_of_cert cert certCost
  let K := (G.subroutines.childComponents G.gammaTable G.reconstruct hC (prepSize_of_prep prep prepCost)).toGreedy
    G.loop
  { prepBudget := prepBudget
    prep := prep
    prepCost := prepCost
    certBudget := certBudget
    cert := cert
    certCost := certCost
    greedyBudget := K.budget
    greedy := K.stage
    greedyCost := K.budget_cost hC
    mainBudget := mainBudget
    main := main
    mainCost := mainCost
    outputBudget := outputBudget
    output := output
    outputCost := outputCost }

end NearQuarticWires.Greedy
