import Proof.Quartic.Greedy.Solve

/-!
# The exact systems of a child evaluation, listed

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

For a column `z`, a pattern `σ`, a digit vector `δ` and a part `s` of the weights, the reconstruction stage writes
one base exact system (`Interfaces.Formats.SysReq`):

* its points are the points of the box `Bx(δ) = ∏_{j ∈ 𝒥} Bx_j(δ^{(j)})`, listed coordinate by coordinate
  (`boxPoints`): the first coordinate runs over the integer interval of `Bx_1` (or `{0}` when `1 ∉ 𝒥`), and for each
  of its values the second coordinate runs over the interval of `Bx_2`;
* its rows are the equations `H_p(ρ_Y) = 𝒩^±(z)`, for the primes `p ∈ 𝒫` in increasing order and the residue vectors
  `ρ_Y` listed coordinate by coordinate (`systemRows`).

`systemOf_encodes`: this system encodes the system of Step 3 (`Greedy.SystemEncodes`), so every exact solver returns
`v^±_{z,σ,δ}` on it (`Greedy.solvedValue_eq`). The values are integers; the reconstruction reads the numerator of the
value at the point `0` (`solvedNum`), and `childObjective_eq_solvedNum` writes the child objective
`Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ (v⁺ - v⁻)` with these numerators. The right side of each row is an entry of a printed
table (`systemRow_eq_printTable`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open Finset
open NearQuarticWires.Greedy
open NearCubicGates.Close.Interfaces.Formats (SysReq SolveMachine)

/-! ## Integer intervals -/

/-- The integers `lo, lo + 1, …, hi`, in increasing order (empty when `hi < lo`). -/
def intervalList (lo hi : ℤ) : List ℤ := (List.range (hi + 1 - lo).toNat).map fun i : ℕ => lo + (i : ℤ)

theorem mem_intervalList {lo hi x : ℤ} : x ∈ intervalList lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  unfold intervalList
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi', rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(x - lo).toNat, by omega, by omega⟩

theorem intervalList_nodup (lo hi : ℤ) : (intervalList lo hi).Nodup := by
  unfold intervalList
  refine List.Nodup.map (fun a b h => ?_) List.nodup_range
  simpa using h

theorem intervalList_length (lo hi : ℤ) : (intervalList lo hi).length = (hi + 1 - lo).toNat := by
  simp [intervalList]

/-! ## The points of a box -/

section Box

variable (C : Algorithm.CellCall)

/-- The two coordinates of a pair as an integer list (the point format of `Interfaces.Formats.SysReq`). -/
def pairList (ab : ℤ × ℤ) : List ℤ := [ab.1, ab.2]

theorem pairList_injective : Function.Injective pairList := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [pairList, List.cons.injEq, and_true] at h
  rw [h.1, h.2]

/-- The coordinate `j` of the box `Bx(δ)` of column `z` (`lem:certify`(d), paper/paper.tex, and
Step 3), as a list: the interval
`[⌈(M_1K(δ^{(j)}) - Λ + 1)/A⌉, ⌊(M_1K(δ^{(j)}) + Λ - 1)/A⌋] ∩ [-2mG_j, 2mG_j]` for a circuit `j ∈ 𝒥`, and `[0]`
otherwise. -/
def boxAxis (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (j : Fin 2) : List ℤ :=
  if j ∈ (C.column z).circuits then
    intervalList
      (max (NearCubicGates.ScoreBox.lower ((C.column z).M * Walks.digitValue (C.column z).rate (δ j))
        (C.column z).A 0 (C.column z).Lambda) (-(((2 * Algorithm.traceOrder : ℕ) : ℤ) * (C.G j : ℤ))))
      (min (NearCubicGates.ScoreBox.upper ((C.column z).M * Walks.digitValue (C.column z).rate (δ j))
        (C.column z).A 0 (C.column z).Lambda) (((2 * Algorithm.traceOrder : ℕ) : ℤ) * (C.G j : ℤ)))
  else [0]

theorem mem_boxAxis (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (j : Fin 2) (x : ℤ) :
    x ∈ boxAxis C z δ j ↔ x ∈ (if j ∈ (C.column z).circuits then
      Walks.fullBox ((C.column z).M * Walks.digitValue (C.column z).rate (δ j)) (C.column z).A
        (C.column z).Lambda ((2 * Algorithm.traceOrder : ℕ) * (C.G j : ℤ))
    else ({0} : Finset ℤ)) := by
  unfold boxAxis
  split
  · rw [mem_intervalList]
    unfold Walks.fullBox
    rw [Finset.mem_Icc]
  · simp

theorem boxAxis_nodup (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (j : Fin 2) :
    (boxAxis C z δ j).Nodup := by
  unfold boxAxis
  split
  · exact intervalList_nodup _ _
  · exact List.nodup_singleton 0

/-- **The points of the box `Bx(δ)`** of column `z` (Step 3 of `sec:algorithm`): the pairs of the two coordinate lists, the
first coordinate outermost. -/
def boxPoints (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) : List (List ℤ) :=
  (boxAxis C z δ 0 ×ˢ boxAxis C z δ 1).map pairList

theorem boxPoints_nodup (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) : (boxPoints C z δ).Nodup :=
  ((boxAxis_nodup C z δ 0).product (boxAxis_nodup C z δ 1)).map pairList_injective

theorem mem_boxPoints (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (u : List ℤ) :
    u ∈ boxPoints C z δ ↔ ∃ y ∈ C.box z δ, pointList y = u := by
  classical
  unfold boxPoints
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [List.mem_product] at hab
    refine ⟨![a, b], ?_, rfl⟩
    unfold Algorithm.CellCall.box
    rw [Fintype.mem_piFinset]
    intro j
    fin_cases j
    · exact (mem_boxAxis C z δ 0 a).mp hab.1
    · exact (mem_boxAxis C z δ 1 b).mp hab.2
  · rintro ⟨y, hy, rfl⟩
    unfold Algorithm.CellCall.box at hy
    rw [Fintype.mem_piFinset] at hy
    refine ⟨(y 0, y 1), ?_, rfl⟩
    rw [List.mem_product]
    exact ⟨(mem_boxAxis C z δ 0 _).mpr (hy 0), (mem_boxAxis C z δ 1 _).mpr (hy 1)⟩

end Box

/-! ## The rows of a system -/

section Rows

variable (C : Algorithm.CellCall)

/-- The coordinate `j` of the residue vectors `ρ_Y` modulo `p` (Step 3 of `sec:algorithm`): `0, 1, …, p - 1` for a
circuit `j ∈ 𝒥`, and `[0]` otherwise. -/
def residueAxis (z : Fin C.ncol) (p : ℕ) (j : Fin 2) : List ℤ :=
  if j ∈ (C.column z).circuits then (List.range p).map Int.ofNat else [0]

/-- The residue vectors `ρ_Y ∈ (ℤ/p)^{𝒥}` of column `z`, as representatives in `[0, p)`, the first coordinate
outermost. -/
def residueList (z : Fin C.ncol) (p : ℕ) : List (Fin 2 → ℤ) :=
  (residueAxis C z p 0 ×ˢ residueAxis C z p 1).map fun ab => ![ab.1, ab.2]

theorem mem_residueAxis (z : Fin C.ncol) (p : ℕ) (j : Fin 2) (x : ℤ) :
    x ∈ residueAxis C z p j ↔ x ∈ (if j ∈ (C.column z).circuits then Finset.Ico (0 : ℤ) p else ({0} : Finset ℤ)) := by
  unfold residueAxis
  split
  · rw [Finset.mem_Ico, List.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [List.mem_range] at hi
      exact ⟨Int.natCast_nonneg i, by simp only [Int.ofNat_eq_natCast]; exact_mod_cast hi⟩
    · rintro ⟨h0, h1⟩
      exact ⟨x.toNat, List.mem_range.mpr (by omega), by simp [Int.toNat_of_nonneg h0]⟩
  · simp

theorem mem_residueList (z : Fin C.ncol) (p : ℕ) (ρ : Fin 2 → ℤ) :
    ρ ∈ residueList C z p ↔ ρ ∈ C.residueVectors z p := by
  classical
  unfold residueList Algorithm.CellCall.residueVectors
  rw [List.mem_map, Fintype.mem_piFinset]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [List.mem_product] at hab
    intro j
    fin_cases j
    · exact (mem_residueAxis C z p 0 a).mp hab.1
    · exact (mem_residueAxis C z p 1 b).mp hab.2
  · intro h
    refine ⟨(ρ 0, ρ 1), List.mem_product.mpr ⟨(mem_residueAxis C z p 0 _).mpr (h 0),
      (mem_residueAxis C z p 1 _).mpr (h 1)⟩, ?_⟩
    funext j
    fin_cases j <;> rfl

/-- The primes `p ∈ 𝒫` in increasing order (the order of `Program.parametersWord`). -/
noncomputable def primeList : List ℕ := C.primes.sort (· ≤ ·)

theorem mem_primeList (p : ℕ) : p ∈ primeList C ↔ p ∈ C.primes := Finset.mem_sort _

/-- **The rows of the system** of column `z`, pattern `σ` and digit vector `δ` for the weight `g` (Step 3,
`sec:algorithm`, paper/paper.tex): the equations `H_p(ρ_Y) = 𝒩(z)`, the primes outermost. -/
noncomputable def systemRows (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ) (z : Fin C.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (C.J + 1) → ℤ) : List (ℕ × List ℕ × ℕ) :=
  (primeList C).flatMap fun p => (residueList C z p).map fun ρ => systemRow C g z σ δ p ρ

theorem mem_systemRows (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ) (z : Fin C.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (row : ℕ × List ℕ × ℕ) :
    row ∈ systemRows C g z σ δ ↔ ∃ p ∈ C.primes, ∃ ρ ∈ C.residueVectors z p, row = systemRow C g z σ δ p ρ := by
  unfold systemRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hrow⟩
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hrow
    exact ⟨p, (mem_primeList C p).mp hp, ρ, (mem_residueList C z p ρ).mp hρ, rfl⟩
  · rintro ⟨p, hp, ρ, hρ, rfl⟩
    exact ⟨p, (mem_primeList C p).mpr hp, List.mem_map.mpr ⟨ρ, (mem_residueList C z p ρ).mpr hρ, rfl⟩⟩

/-- **The base exact system** of Step 3 (`sec:algorithm`, paper/paper.tex) for the part `s` of the weights at the
prefix `π`, the column `z`, the pattern `σ` and the digit vector `δ`: the points of `Bx(δ)` and the equations
`H_p(ρ_Y) = 𝒩^±(z)`. -/
noncomputable def systemOf (π : List Bool) (s : Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : SysReq where
  pts := boxPoints C z δ
  rows := systemRows C (splitWeight C π s) z σ δ

/-- **The listed system encodes the system of Step 3.** -/
theorem systemOf_encodes (π : List Bool) (s : Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : SystemEncodes C (systemOf C π s z σ δ) π s z σ δ where
  nodup := boxPoints_nodup C z δ
  mem_pts := mem_boxPoints C z δ
  rows_sound := fun row h => (mem_systemRows C _ z σ δ row).mp h
  rows_complete := fun p hp ρ hρ => (mem_systemRows C _ z σ δ _).mpr ⟨p, hp, ρ, hρ, rfl⟩

end Rows

/-! ## The right sides are entries of the printed tables -/

/-- **The right side of a row is an entry of a printed table** (`lem:print`(a), `lem:residue`): the row of the prime
`p` and the residue vector `ρ_Y` in the system of the part `s`, the column `z`, the pattern `σ` and the digit vector `δ`
carries entry `z` of the table printed for `(s, σ, p, δ, ρ_Y)`. -/
theorem systemRow_eq_printTable {B1 B2 : ℕ} (r : PrintRequest B1 B2) (z : Fin r.child.cellCall.ncol) :
    systemRow r.child.cellCall (splitWeight r.child.cellCall r.child.seedPrefix r.sign) z r.pattern r.digits r.prime
        r.residues =
      (r.prime, [(r.residues 0).toNat, (r.residues 1).toNat],
        ((printTable r)[z.val]'(by simp [printTable])).toNat) := by
  simp [systemRow, printTable]

/-! ## The child objective from the numerators of the solved values -/

/-- The integer read off the answer of an exact solver: the numerator of the value at the point `0`
(`Interfaces.Formats.solveWord` writes each value as `ratWord`, numerator first). -/
noncomputable def solvedNum (S : SolveMachine) (sys : SysReq) : ℤ := (solvedValue S sys).num

/-- **The child objective from the solver's numerators** (Step 3, `sec:algorithm`, paper/paper.tex): for every child
evaluation and every exact solver,
`Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ (v⁺_{z,σ,δ} - v⁻_{z,σ,δ})`, where `v^±` is the numerator of the value at `0` returned
by the solver on the listed system of the part `±` (`systemOf`). -/
theorem childObjective_eq_solvedNum {B1 B2 : ℕ} (S : SolveMachine) (q : ChildRequest B1 B2) :
    childObjective q = ∑ z ∈ q.cellCall.certifiedColumns, ∑ σ : Cycle.SignPattern Algorithm.traceOrder,
      Cycle.kappa Algorithm.traceOrder σ * ∑ δ ∈ q.cellCall.digitVectors z,
        (solvedNum S (systemOf q.cellCall q.seedPrefix true z σ δ) -
          solvedNum S (systemOf q.cellCall q.seedPrefix false z σ δ)) := by
  have H : q.cellCall.ReconstructionHypotheses := reconstructionHypotheses_of_dispatch q.dispatched q.witness
  rw [childObjective_split]
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : Cycle.kappa Algorithm.traceOrder σ = 0
  · simp [hσ]
  · congr 1
    refine Finset.sum_congr rfl fun δ hδ => ?_
    have h1 := solvedValue_eq _ S _ H _ q.prefix_le true z hz σ hσ δ hδ (systemOf_encodes _ _ true z σ δ)
    have h2 := solvedValue_eq _ S _ H _ q.prefix_le false z hz σ hσ δ hδ (systemOf_encodes _ _ false z σ δ)
    unfold solvedNum
    rw [h1, h2, Rat.num_intCast, Rat.num_intCast]

end NearQuarticWires.Reconstruct
