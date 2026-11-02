import Proof.Quartic.Reconstruct.Gather

/-!
# The gathering stage in two parts

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The stage `ReconstructPhases.systems` turns the printed tables (`tablesWord`) into the exact systems
(`systemsWord`). It is the composition of two word functions:

1. `gather` (the transposition): for every listed system `(s, σ, δ, z)` of `systemList`, the part, the digit vector
   and the rows of the system, whose right sides are the entries `z` of the tables printed for `(s, σ, δ)`, in the
   order of the primes `p ∈ 𝒫` and the residue vectors `ρ_Y` (`countsOf`, `countsOf_eq_tables`): `gatheredWord`.
2. `emit` (the systems): for every gathered item, the tag of the system and its word: the points of the box
   `Bx(δ)` and the rows `(p, ρ_Y, 𝒩(z))` (`systemAt_rows_eq`): `systemsWord`.

`systemsOfSplit` composes them into the field `ReconstructPhases.systems`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord)

variable {B1 B2 : ℕ}

section Gathered

variable (q : ChildRequest B1 B2)

/-- The right sides of the rows of a listed system, as natural numbers, in the order of the rows. -/
noncomputable def countsOf (x : SystemIndex q) : List ℕ := (systemAt q x).rows.map fun row => row.2.2

/-- The indices `(p, ρ_Y)` of the rows of every system of a child: the primes `p ∈ 𝒫` in increasing order and the
residue vectors modulo `p`. -/
noncomputable def rowIndexList : List (ℕ × (Fin 2 → ℤ)) :=
  (primeList q.cellCall).flatMap fun p => (residueListOf q p).map fun ρ => (p, ρ)

/-- **The rows of a listed system from its indices and its counts.** -/
theorem systemAt_rows_eq (x : SystemIndex q) :
    (systemAt q x).rows = (rowIndexList q).zipWith (fun pρ c => (pρ.1, [(pρ.2 0).toNat, (pρ.2 1).toNat], c))
      (countsOf q x) := by
  have hrows : (systemAt q x).rows = (rowIndexList q).map fun pρ =>
      systemRow q.cellCall (splitWeight q.cellCall q.seedPrefix x.1) x.2.2.2 x.2.1 x.2.2.1 pρ.1 pρ.2 := by
    show systemRows q.cellCall _ x.2.2.2 x.2.1 x.2.2.1 = _
    unfold systemRows rowIndexList
    rw [List.map_flatMap]
    refine List.flatMap_congr fun p _ => ?_
    rw [residueList_eq, List.map_map]
    rfl
  unfold countsOf
  rw [hrows, List.map_map, List.zipWith_map_right, List.zipWith_self]
  rfl

/-- **The counts of a listed system are entries of the printed tables** (`lem:print`(a), `lem:residue`): entry `z`
of the table printed for `(s, σ, p, δ, ρ_Y)`, for the rows `(p, ρ_Y)` in order. -/
theorem countsOf_eq_tables (x : SystemIndex q) :
    countsOf q x = (primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ =>
      ((printTable (tableOf q x p.1 ((mem_primeList _ _).mp p.2) ρ)).getD x.2.2.2.val 0).toNat := by
  unfold countsOf
  rw [systemAt_rows, List.map_flatMap]
  refine List.flatMap_congr fun p _ => ?_
  rw [List.map_map]
  rfl

/-- The word of one row `(p, ρ_Y, 𝒩)` of a system, as in `Interfaces.Formats.sysWord`. -/
def rowWord (row : ℕ × List ℕ × ℕ) : List Bool := natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2

/-- One gathered item: the part, the digit vector and the rows of a listed system (the rows carry the counts, the
entries of the printed tables, `countsOf_eq_tables`). -/
noncomputable def gatheredItem (x : SystemIndex q) : List Bool :=
  bitWord x.1 ++
    listWord NearCubicGates.Close.Interfaces.intWord
      (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (q.cellCall.J + 1) => x.2.2.1 i j).flatten ++
    listWord rowWord (systemAt q x).rows

/-- After `gather`: the context and the gathered items of the listed systems. -/
noncomputable def gatheredWord : List Bool :=
  contextWord q ++ listWord (gatheredItem q) (systemList q)

end Gathered

/-- **The gathering stage from its two parts** (Step 3 of `sec:algorithm`): a transposition `tablesWord ↦
gatheredWord` and an emission `gatheredWord ↦ systemsWord`, each within `K (n+1)^e` times the cost of the stage,
give the field `systems` of `ReconstructPhases` with the constant `8K + 12`. -/
noncomputable def systemsOfSplit (K e : ℕ)
    (gather : WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (gatheredWord q))
      (fun q => K * (q.call.n + 1) ^ e * systemsCost q))
    (emit : WordFunction (ChildRequest B1 B2) gatheredWord (fun q => frame (systemsWord q))
      (fun q => K * (q.call.n + 1) ^ e * systemsCost q)) :
    WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (systemsWord q))
      (fun q => (8 * K + 12) * (q.call.n + 1) ^ e * systemsCost q) :=
  WordFunction.enlargeBudget (WordFunction.pipe gather emit) (fun q => by
    have h1 : 1 ≤ (q.call.n + 1) ^ e * systemsCost q :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by unfold systemsCost; omega))
    change 4 * (K * (q.call.n + 1) ^ e * systemsCost q) + 4 * (K * (q.call.n + 1) ^ e * systemsCost q) + 12 ≤
      (8 * K + 12) * (q.call.n + 1) ^ e * systemsCost q
    nlinarith)

end NearQuarticWires.Reconstruct
