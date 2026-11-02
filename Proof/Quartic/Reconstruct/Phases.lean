import Proof.Quartic.Reconstruct.Lists
import Proof.Quartic.Reconstruct.Sizes
import Proof.Foundations.OrdinaryMachine

/-!
# The reconstruction stage as five word functions

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The reconstruction stage of a child evaluation (`Greedy.ReconstructControl`) maps the word `gammaWord` (the child
input and the coefficient table) to `intWord Ψ̃(π)`. It is the composition (`Program.WordFunction.pipe`) of five word
functions, each writing the next word framed:

1. `prints`: the print inputs. For every table `(s, σ, δ, p, ρ_Y)` of `printList`, its index word and its input
   `printInput` (the word after parameter preparation, the coefficient table, the index word): `printsWord`.
2. `tables`: the printed tables. For every word function printing one table (`lem:print`(a), `lem:residue`),
   each print input is replaced by its table `z ↦ 𝒩(z)`: `tablesWord`.
3. `systems`: the exact systems. For every system `(s, σ, δ, z)` of `systemList`, its tag (the coefficient
   `(±1)κ_σ` and the position of the point `0`) and its word `sysWord` (`systemOf`; its right sides are entries of
   the printed tables, `systemRow_eq_printTable`): `systemsWord`.
4. `solved`: the answers. For every exact solver, each system is replaced by the solver's answer: `solvedWord`.
5. `total`: the sum `Σ (±1)κ_σ v` over the answers (`childObjective_eq_systemList`): `intWord Ψ̃(π)`.

The two stages that call a subroutine (`tables`, `solved`) take it as an argument, as `ReconstructControl` does; the
three others are single word functions. The words read by the three
stages without subroutine (`gammaWord`, `tablesWord`, `solvedWord`) are unframed concatenations of self-delimiting
fields starting with `natWord n`; the words read by the two calling stages (`printsWord`, `systemsWord`) carry a frame
around each request and around the passed context.

`ReconstructPhases.control`: **the five stages give `ReconstructControl`**, with the constant `596 K + 1020`, the
exponent of the stages, and the size exponent `sizeExp` of the table indices and the systems (`Sizes`). The costs
of the stages are the parts of the cost of `prop:time` that each one spends: the print inputs (`printsCost`), the
printing (`tablesCost`), the gathering of the tables into systems (`systemsCost`), and the solving and the sum
(`solvedCost`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces.Formats (SysReq SolveMachine sysWord solveWord)

variable {B1 B2 : ℕ}

/-! ## The size exponent -/

/-- The exponent of the sizes of the table indices and of the systems (`printIndexWord_length_le`,
`sysWord_length_le`). -/
noncomputable def sizeExp (B1 B2 : ℕ) : ℕ :=
  max (Classical.choose (printIndexWord_length_le B1 B2)) (Classical.choose (sysWord_length_le B1 B2))

theorem mem_residueListOf {q : ChildRequest B1 B2} {p : ℕ} {ρ : Fin 2 → ℤ} (hρ : ρ ∈ residueListOf q p) :
    ρ ∈ residueSet q p := by
  classical
  have hax : ∀ (c : Fin 2) (x : ℤ), x ∈ (if c ∈ Builder.circuitSet q.call then (List.range p).map Int.ofNat
      else [0]) → x ∈ (if c ∈ Builder.circuitSet q.call then Finset.Ico (0 : ℤ) p else {0}) := by
    intro c x hx
    by_cases hc : c ∈ Builder.circuitSet q.call
    · rw [if_pos hc] at hx
      rw [if_pos hc, Finset.mem_Ico]
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hi
      exact ⟨by simp, by simp only [Int.ofNat_eq_natCast]; exact_mod_cast hi⟩
    · rw [if_neg hc] at hx
      rw [if_neg hc]
      simpa using hx
  have h : ρ ∈ ((if (0 : Fin 2) ∈ Builder.circuitSet q.call then (List.range p).map Int.ofNat else [0]) ×ˢ
      (if (1 : Fin 2) ∈ Builder.circuitSet q.call then (List.range p).map Int.ofNat else [0])).map
        (fun ab => ![ab.1, ab.2]) := hρ
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp h
  rw [List.mem_product] at hab
  show _ ∈ Fintype.piFinset _
  rw [Fintype.mem_piFinset]
  intro j
  fin_cases j
  · exact hax 0 a hab.1
  · exact hax 1 b hab.2

theorem mem_printList {q : ChildRequest B1 B2} {r : PrintRequest B1 B2} (hr : r ∈ printList q) :
    ∃ (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ)
      (p : {p // p ∈ primeList q.cellCall}) (ρ : Fin 2 → ℤ), δ ∈ digitSet q ∧ ρ ∈ residueSet q p.1 ∧
      r = printRequestOf q s σ δ p ρ := by
  obtain ⟨s, -, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨σ, -, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨δ, hδ, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨p, -, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨ρ, hρ, hr⟩ := List.mem_map.mp hr
  exact ⟨s, σ, δ, p, ρ, (mem_digitList q δ).mp hδ, mem_residueListOf hρ, hr.symm⟩

/-- **Every printed table has an index word of size at most `(n+1)^{sizeExp}`.** -/
theorem printIndexWord_le_sizeExp {q : ChildRequest B1 B2} {r : PrintRequest B1 B2} (hr : r ∈ printList q) :
    (printIndexWord r).length ≤ (r.child.call.n + 1) ^ sizeExp B1 B2 := by
  obtain ⟨s, σ, δ, p, ρ, hδ, hρ, hr⟩ := mem_printList hr
  subst hr
  exact (Classical.choose_spec (printIndexWord_length_le B1 B2) (printRequestOf q s σ δ p ρ)
    ((mem_primeList _ _).mp p.2) hδ hρ).trans (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))

/-- **Every listed system has a word of size at most `(n+1)^{sizeExp}`.** -/
theorem sysWord_le_sizeExp (q : ChildRequest B1 B2) (x : SystemIndex q) :
    (sysWord (systemAt q x)).length ≤ (q.call.n + 1) ^ sizeExp B1 B2 := by
  exact (Classical.choose_spec (sysWord_length_le B1 B2) q q.seedPrefix x.1 x.2.2.2 x.2.1 x.2.2.1).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _))

/-! ## The words between the stages -/

section Words

variable (q : ChildRequest B1 B2)

/-- The number of tables in one group `(s, σ, δ)` of `printList`: one per prime `p ∈ 𝒫` and residue vector `ρ_Y`
modulo `p` (`prop:time`). -/
noncomputable def tablesPerGroup : ℕ := ((primeList q.cellCall).flatMap (residueListOf q)).length

/-- The context of the later stages, every field self-delimiting and unframed: `natWord n`; the parameters `M_1`, `A`,
`Λ` and the last digit index `J` of `sec:params`; the rates (the factor list); whether the call has two circuits
(`𝒥 = {1, 2}`); the coordinate bounds `2mG_1`, `2mG_2` of the boxes; the number of columns `n_col = 2^{n-k}`; the
number of tables per group; and the certified columns `Z_c` (one bit per column). -/
noncomputable def contextWord : List Bool :=
  natWord q.call.n ++ natWord q.selected.1.M1 ++ natWord q.selected.1.A ++ natWord q.selected.1.Lambda ++
    natWord q.cellCall.J ++ listWord natWord q.selected.1.factors ++ bitWord (decide (q.call.kind = .pair)) ++
    natWord (2 * Algorithm.traceOrder * Builder.occurrences q.call 0) ++
    natWord (2 * Algorithm.traceOrder * Builder.occurrences q.call 1) ++ natWord q.cellCall.ncol ++
    natWord (tablesPerGroup q) ++ listWord bitWord (certifiedBits q.cellCall)

/-- After `prints`: the framed context and, for every table of `printList`, its framed index word and its framed
print input (the frames delimit the requests of the subroutine). -/
noncomputable def printsWord : List Bool :=
  frame (contextWord q) ++ listWord (fun r => frame (printIndexWord r) ++ frame (printInput r)) (printList q)

/-- After `tables`: the context and, for every table of `printList`, its index word and the table
`z ↦ 𝒩(z)` (`listWord intWord (printTable r)`). -/
noncomputable def tablesWord : List Bool :=
  contextWord q ++
    listWord (fun r => printIndexWord r ++ listWord NearCubicGates.Close.Interfaces.intWord (printTable r))
      (printList q)

/-- The tag of a system: its coefficient `(±1)κ_σ` in `Ψ̃(π)` and the position of the point `0` in its list of
points. -/
noncomputable def systemTag (x : SystemIndex q) : List Bool :=
  NearCubicGates.Close.Interfaces.intWord (systemCoef q x) ++ natWord ((systemAt q x).pts.idxOf [0, 0])

/-- After `systems`: the framed `natWord n` and, for every system of `systemList`, its framed tag and its framed word
(the frames delimit the requests of the solver). -/
noncomputable def systemsWord : List Bool :=
  frame (natWord q.call.n) ++
    listWord (fun x => frame (systemTag q x) ++ frame (sysWord (systemAt q x))) (systemList q)

/-- After `solved`: `natWord n` and, for every system of `systemList`, its tag and the answer of the solver. -/
noncomputable def solvedWord (S : SolveMachine) : List Bool :=
  natWord q.call.n ++
    listWord (fun x => systemTag q x ++ solveWord (S.solve (systemAt q x))) (systemList q)

end Words

/-! ## The costs of the stages -/

section Costs

variable (q : ChildRequest B1 B2)

/-- The cost of `prints`: one copy of the word after parameter preparation, the coefficient table and the indices
per table. -/
noncomputable def printsCost : ℕ :=
  tableCount q * ((prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length +
    (q.call.n + 1) ^ sizeExp B1 B2) + (gammaWord q).length + 1

/-- The cost of `tables`: one printing, one copy of its input and of its `2^{n-k}` entries per table. -/
noncomputable def tablesCost (printBound : Call → List Bool → ℕ) : ℕ :=
  tableCount q * (printBound q.call q.witness + (prepWord B1 B2 q.call q.witness).length +
    (gammaTableWord q).length + q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2) + (gammaWord q).length + 1

/-- The cost of `systems`: the `2^{n-k}` entries of every table, and the rows of every system. -/
noncomputable def systemsCost : ℕ :=
  tableCount q * (q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2) + systemCount q * (rowCount q + 1) +
    (gammaWord q).length + 1

/-- The cost of `solved` and of `total`: the rows and one solve per system. -/
noncomputable def solvedCost (solveBound : Call → List Bool → ℕ) : ℕ :=
  systemCount q * (rowCount q + solveBound q.call q.witness + 1) + (gammaWord q).length + 1

end Costs

/-! ## The five stages -/

/-- **The five stages of the reconstruction** (Step 3, paper/paper.tex; `prop:time`), with a common constant `K` and exponent `e` of their costs. -/
structure ReconstructPhases (B1 B2 : ℕ) where
  /-- The constant of the costs. -/
  K : ℕ
  /-- The exponent of the polynomial factor of the costs. -/
  e : ℕ
  /-- The print inputs of the tables. -/
  prints : WordFunction (ChildRequest B1 B2) gammaWord (fun q => frame (printsWord q))
    (fun q => K * (q.call.n + 1) ^ e * printsCost q)
  /-- The printed tables, for every word function printing one table. -/
  tables : ∀ (printBudget : PrintRequest B1 B2 → ℕ) (printBound : Call → List Bool → ℕ),
    WordFunction (PrintRequest B1 B2) printInput (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) printBudget →
    (∀ r : PrintRequest B1 B2, (printIndexWord r).length ≤ (r.child.call.n + 1) ^ sizeExp B1 B2 →
      printBudget r ≤ printBound r.child.call r.child.witness) →
    WordFunction (ChildRequest B1 B2) printsWord (fun q => frame (tablesWord q))
      (fun q => K * (q.call.n + 1) ^ e * tablesCost q printBound)
  /-- The exact systems gathered from the tables. -/
  systems : WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (systemsWord q))
    (fun q => K * (q.call.n + 1) ^ e * systemsCost q)
  /-- The answers of every exact solver. -/
  solved : ∀ (solver : SolveMachine) (solveBound : Call → List Bool → ℕ),
    (∀ (q : ChildRequest B1 B2) (s : SysReq), (sysWord s).length ≤ (q.call.n + 1) ^ sizeExp B1 B2 →
      solver.budget s ≤ solveBound q.call q.witness) →
    WordFunction (ChildRequest B1 B2) systemsWord (fun q => frame (solvedWord q solver))
      (fun q => K * (q.call.n + 1) ^ e * solvedCost q solveBound)
  /-- The sum `Σ (±1)κ_σ v` over the answers. -/
  total : ∀ (solver : SolveMachine) (solveBound : Call → List Bool → ℕ),
    (∀ (q : ChildRequest B1 B2) (s : SysReq), (sysWord s).length ≤ (q.call.n + 1) ^ sizeExp B1 B2 →
      solver.budget s ≤ solveBound q.call q.witness) →
    WordFunction (ChildRequest B1 B2) (fun q => solvedWord q solver) (fun q => NearCubicGates.Close.Interfaces.intWord (childObjective q))
      (fun q => K * (q.call.n + 1) ^ e * solvedCost q solveBound)

namespace ReconstructPhases

variable (Φ : ReconstructPhases B1 B2)

/-- The cost of `prop:time` for the reconstruction of a child (the cost form of `ReconstructControl`, before its
constant and polynomial factor). -/
noncomputable def stageCost (q : ChildRequest B1 B2) (printBound solveBound : Call → List Bool → ℕ) : ℕ :=
  tableCount q * (printBound q.call q.witness + (prepWord B1 B2 q.call q.witness).length +
      (gammaTableWord q).length + q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2) +
    systemCount q * (rowCount q + solveBound q.call q.witness + 1) + (gammaWord q).length + 1

theorem printsCost_le (q : ChildRequest B1 B2) (printBound solveBound : Call → List Bool → ℕ) :
    printsCost q ≤ stageCost q printBound solveBound := by
  unfold printsCost stageCost
  have := Nat.mul_le_mul_left (tableCount q) (show (prepWord B1 B2 q.call q.witness).length +
    (gammaTableWord q).length + (q.call.n + 1) ^ sizeExp B1 B2 ≤ printBound q.call q.witness +
    (prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length + q.cellCall.ncol +
    (q.call.n + 1) ^ sizeExp B1 B2 by omega)
  omega

theorem tablesCost_le (q : ChildRequest B1 B2) (printBound solveBound : Call → List Bool → ℕ) :
    tablesCost q printBound ≤ stageCost q printBound solveBound := by
  unfold tablesCost stageCost
  omega

theorem systemsCost_le (q : ChildRequest B1 B2) (printBound solveBound : Call → List Bool → ℕ) :
    systemsCost q ≤ stageCost q printBound solveBound := by
  unfold systemsCost stageCost
  have h1 := Nat.mul_le_mul_left (tableCount q) (show q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2 ≤
    printBound q.call q.witness + (prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length +
    q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2 by omega)
  have h2 := Nat.mul_le_mul_left (systemCount q) (show rowCount q + 1 ≤
    rowCount q + solveBound q.call q.witness + 1 by omega)
  omega

theorem solvedCost_le (q : ChildRequest B1 B2) (printBound solveBound : Call → List Bool → ℕ) :
    solvedCost q solveBound ≤ stageCost q printBound solveBound := by
  unfold solvedCost stageCost
  omega

/-- **The reconstruction control from its five stages** (Step 3, paper/paper.tex, with
`prop:time`): the composition `prints ▹ tables ▹ systems ▹ solved ▹ total` maps `gammaWord` to
`intWord Ψ̃(π)` within `(596 K + 1020) (n+1)^e` times the cost of `prop:time`. -/
noncomputable def control : ReconstructControl B1 B2 where
  K := 596 * Φ.K + 1020
  e := Φ.e
  e₀ := sizeExp B1 B2
  program := fun printBudget solver printBound solveBound print hprint hsolve =>
    WordFunction.enlargeBudget
      (WordFunction.pipe Φ.prints
        (WordFunction.pipe (Φ.tables printBudget printBound print hprint)
          (WordFunction.pipe Φ.systems
            (WordFunction.pipe (Φ.solved solver solveBound hsolve) (Φ.total solver solveBound hsolve)))))
      (fun q => by
        have h1 := Nat.mul_le_mul_left (Φ.K * (q.call.n + 1) ^ Φ.e) (printsCost_le q printBound solveBound)
        have h2 := Nat.mul_le_mul_left (Φ.K * (q.call.n + 1) ^ Φ.e) (tablesCost_le q printBound solveBound)
        have h3 := Nat.mul_le_mul_left (Φ.K * (q.call.n + 1) ^ Φ.e) (systemsCost_le q printBound solveBound)
        have h4 := Nat.mul_le_mul_left (Φ.K * (q.call.n + 1) ^ Φ.e) (solvedCost_le q printBound solveBound)
        have hX : 1 ≤ (q.call.n + 1) ^ Φ.e * stageCost q printBound solveBound :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by unfold stageCost; omega))
        change 4 * (Φ.K * (q.call.n + 1) ^ Φ.e * printsCost q) + 4 * (4 * (Φ.K * (q.call.n + 1) ^ Φ.e *
            tablesCost q printBound) + 4 * (4 * (Φ.K * (q.call.n + 1) ^ Φ.e * systemsCost q) +
            4 * (4 * (Φ.K * (q.call.n + 1) ^ Φ.e * solvedCost q solveBound) +
              4 * (Φ.K * (q.call.n + 1) ^ Φ.e * solvedCost q solveBound) + 12) + 12) + 12) + 12 ≤
          (596 * Φ.K + 1020) * (q.call.n + 1) ^ Φ.e * stageCost q printBound solveBound
        nlinarith)

end ReconstructPhases

end NearQuarticWires.Reconstruct
