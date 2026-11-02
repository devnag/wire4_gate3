import Proof.Quartic.Reconstruct.SystemsSplit

/-!
# The gathering of the printed tables: the words by groups

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The printed tables come in groups `(s, σ, δ)` (`groupList`): one table per prime `p ∈ 𝒫` and residue vector `ρ_Y`
(`rowList`, `printList_groups`). The listed systems of a group are its certified columns when `κ_σ ≠ 0`
(`systemList_groups`). Hence the input of the gathering is the context followed by the groups of tables
(`tablesWord_groups`), and its output the context followed by the gathered items of the groups
(`gatheredWord_groups`): the gathering works group by group.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct

theorem activePatterns_length : activePatterns.length = 128 := by decide

variable {B1 B2 : ℕ}

section Groups

variable (q : ChildRequest B1 B2)

/-- A group of tables: the part, the pattern and the digit vector. -/
abbrev Grp : Type := Bool × Cycle.SignPattern Algorithm.traceOrder × (Fin 2 → Fin (q.cellCall.J + 1) → ℤ)

/-- The groups, in the order of `printList`. -/
noncomputable def groupList : List (Grp q) :=
  [true, false].flatMap fun s => patternList.flatMap fun σ => (digitList q).map fun δ => (s, σ, δ)

/-- The rows of every group: the primes `p ∈ 𝒫` (increasing) and the residue vectors modulo `p`. -/
noncomputable def rowList : List ({p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ)) :=
  (primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ => (p, ρ)

/-- The table of a group and a row. -/
noncomputable def tableAt (G : Grp q) (pr : {p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ)) : PrintRequest B1 B2 :=
  printRequestOf q G.1 G.2.1 G.2.2 pr.1 pr.2

/-- Whether a pattern enters `Ψ̃(π)`. -/
def active (σ : Cycle.SignPattern Algorithm.traceOrder) : Bool := decide (Cycle.kappa Algorithm.traceOrder σ ≠ 0)

theorem printList_groups : printList q = (groupList q).flatMap fun G => (rowList q).map (tableAt q G) := by
  unfold printList groupList
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun s _ => ?_
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun σ _ => ?_
  rw [List.flatMap_map]
  refine List.flatMap_congr fun δ _ => ?_
  simp only [rowList, tableAt, List.map_flatMap, List.map_map]
  rfl

theorem filter_flatMap' {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap fun a => if p a then f a else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem systemList_groups : systemList q = (groupList q).flatMap fun G =>
    if active G.2.1 then (certList q).map fun z => ((G.1, G.2.1, G.2.2, z) : SystemIndex q) else [] := by
  unfold systemList groupList activePatterns active
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun s _ => ?_
  rw [filter_flatMap', List.flatMap_assoc]
  refine List.flatMap_congr fun σ _ => ?_
  rw [List.flatMap_map]
  split <;> simp

/-! ## The words -/

/-- The word of one printed table: its indices and the table. -/
noncomputable def tableItemWord (r : PrintRequest B1 B2) : List Bool :=
  printIndexWord r ++ listWord NearCubicGates.Close.Interfaces.intWord (printTable r)

/-- The input of a group: its tables. -/
noncomputable def groupIn (G : Grp q) : List Bool := ((rowList q).map (tableAt q G)).flatMap tableItemWord

/-- The output of a group: the gathered items of its systems. -/
noncomputable def groupOut (G : Grp q) : List Bool :=
  if active G.2.1 then (certList q).flatMap fun z => gatheredItem q (G.1, G.2.1, G.2.2, z) else []

theorem tablesWord_groups : tablesWord q = contextWord q ++ natWord (printList q).length ++
    (groupList q).flatMap (groupIn q) := by
  have h : (printList q).flatMap tableItemWord = (groupList q).flatMap (groupIn q) := by
    rw [printList_groups, List.flatMap_assoc]
    rfl
  show contextWord q ++ (natWord (printList q).length ++ (printList q).flatMap tableItemWord) = _
  rw [h, List.append_assoc]

theorem gatheredWord_groups : gatheredWord q = contextWord q ++ natWord (systemList q).length ++
    (groupList q).flatMap (groupOut q) := by
  have h : (systemList q).flatMap (gatheredItem q) = (groupList q).flatMap (groupOut q) := by
    rw [systemList_groups, List.flatMap_assoc]
    refine List.flatMap_congr fun G _ => ?_
    unfold groupOut
    split <;> simp [List.flatMap_map]
  show contextWord q ++ (natWord (systemList q).length ++ (systemList q).flatMap (gatheredItem q)) = _
  rw [h, List.append_assoc]

end Groups

end NearQuarticWires.Reconstruct.GatherProg
