import Proof.Quartic.Greedy.Split

/-!
# The exact systems of Step 3 as base exact systems

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time` (each system
has at most `L_w^2` unknowns, `0/1` matrix entries and right sides of `O(B_N)` bits, solved exactly).

The base library solves exact systems given as a list of integer points and a list of rows `(q, ρ, b)`, each row
asking that the values at the points congruent to `ρ` modulo `q` sum to the natural number `b`
(`Interfaces.Formats.SysReq`, `SysSolves`); a `SolveMachine` returns a solution when one exists.

`SystemEncodes sys C π s z σ δ` says that `sys` lists the points of the box `Bx(δ)`, each once, and the equations
`H_p(ρ_Y) = 𝒩^±(z)` for all `p ∈ 𝒫` and residue vectors `ρ_Y` of the part `s` of the weights (in any order, with
repetitions allowed). The right sides are natural because the recovered counts of a part are nonnegative.

* `solvedValue_eq`: on a certified column, for `κ_σ ≠ 0` and a digit vector `δ`, every `SolveMachine` returns a
  solution of every encoding system, and its value at the point `0` is `v^±_{z,σ,δ}` (and `0` if `0 ∉ Bx(δ)`, as in
  the paper).
* `childObjective_solved`: hence `Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ (v⁺ - v⁻)` with the values returned by the solver,
  for every child evaluation.
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open Finset
open NearCubicGates.Close.Interfaces.Formats (SysReq SysSolves SolveMachine inClass)

/-! ## Lists of points and values -/

/-- A point `y ∈ ℤ²` as the integer list `[y_1, y_2]`. -/
def pointList (y : Fin 2 → ℤ) : List ℤ := [y 0, y 1]

theorem pointList_injective : Function.Injective pointList := by
  intro a b h
  simp only [pointList, List.cons.injEq, and_true] at h
  funext j
  fin_cases j
  · exact h.1
  · exact h.2

/-- The value at the point `u` of a list of values `F` over a list of points `pts`. -/
def pointValue (pts : List (List ℤ)) (F : List ℚ) (u : List ℤ) : ℚ :=
  (((pts.zip F).filter fun uf => decide (uf.1 = u)).map Prod.snd).sum

theorem pointValue_cons (a : List ℤ) (as : List (List ℤ)) (f : ℚ) (fs : List ℚ) (u : List ℤ) :
    pointValue (a :: as) (f :: fs) u = (if a = u then f else 0) + pointValue as fs u := by
  unfold pointValue
  rw [List.zip_cons_cons, List.filter_cons]
  by_cases h : a = u
  · simp [h]
  · simp [h]

theorem pointValue_of_not_mem (pts : List (List ℤ)) (F : List ℚ) (u : List ℤ) (hu : u ∉ pts) :
    pointValue pts F u = 0 := by
  unfold pointValue
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · rintro ⟨a, b⟩ huf
    have ha := (List.of_mem_zip huf).1
    simp only [decide_eq_true_eq]
    rintro rfl
    exact hu ha

/-- The sum of the values at the points satisfying `P` is the sum over these points of `pointValue`. -/
theorem sum_filter_zip (P : List ℤ → Bool) :
    ∀ (pts : List (List ℤ)) (F : List ℚ), pts.Nodup → F.length = pts.length →
      (((pts.zip F).filter fun uf => P uf.1).map Prod.snd).sum =
        ∑ u ∈ pts.toFinset.filter (fun u => P u = true), pointValue pts F u
  | [], _, _, _ => by simp
  | a :: as, [], _, hl => by simp at hl
  | a :: as, f :: fs, hnd, hl => by
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    have hnd' : as.Nodup := (List.nodup_cons.mp hnd).2
    have hl' : fs.length = as.length := by simpa using hl
    have ih := sum_filter_zip P as fs hnd' hl'
    have hrest : ∑ u ∈ as.toFinset.filter (fun u => P u = true), pointValue (a :: as) (f :: fs) u =
        ∑ u ∈ as.toFinset.filter (fun u => P u = true), pointValue as fs u := by
      refine Finset.sum_congr rfl fun u hu => ?_
      have hu' : u ∈ as := List.mem_toFinset.mp (Finset.mem_filter.mp hu).1
      have hne : ¬ a = u := fun h => ha (h ▸ hu')
      rw [pointValue_cons, if_neg hne, zero_add]
    rw [List.zip_cons_cons, List.filter_cons, List.toFinset_cons, Finset.filter_insert]
    by_cases hP : P a = true
    · rw [if_pos hP, if_pos hP, List.map_cons, List.sum_cons, Finset.sum_insert]
      · rw [hrest, ih, pointValue_cons, if_pos rfl, pointValue_of_not_mem as fs a ha, add_zero]
      · intro h
        exact ha (List.mem_toFinset.mp (Finset.mem_filter.mp h).1)
    · rw [if_neg hP, if_neg hP, hrest, ih]

/-- The values of a function listed over a list of distinct points. -/
theorem pointValue_map (f : List ℤ → ℚ) :
    ∀ (pts : List (List ℤ)), pts.Nodup → ∀ u ∈ pts, pointValue pts (pts.map f) u = f u
  | [], _, u, hu => by simp at hu
  | a :: as, hnd, u, hu => by
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    have hnd' : as.Nodup := (List.nodup_cons.mp hnd).2
    rw [List.map_cons, pointValue_cons]
    by_cases h : a = u
    · subst h
      rw [if_pos rfl, pointValue_of_not_mem as _ a ha, add_zero]
    · rw [if_neg h, zero_add]
      exact pointValue_map f as hnd' u ((List.mem_cons.mp hu).resolve_left (Ne.symm h))

theorem natCast_toNat {N : ℤ} (h : 0 ≤ N) : ((N.toNat : ℕ) : ℚ) = (N : ℚ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

/-! ## The encoding of the systems of Step 3 -/

section Encoding

variable (C : Algorithm.CellCall)

/-- The row of the equation `H_p(ρ_Y) = 𝒩(z)` (Step 3 of `sec:algorithm`) for an arbitrary weight `g`: the modulus
`p`, the residue vector `ρ_Y` and the recovered count as a natural number. -/
noncomputable def systemRow (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ) (z : Fin C.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (p : ℕ) (ρY : Fin 2 → ℤ) :
    ℕ × List ℕ × ℕ :=
  (p, [(ρY 0).toNat, (ρY 1).toNat], (recoveredCountOf C g z σ p δ ρY).toNat)

/-- **A base exact system encodes the system of Step 3** (`sec:algorithm`, paper/paper.tex) for the part `s` of the
weights at the column `z`, the pattern `σ` and the digit vector `δ`: its points are the points of `Bx(δ)`, each
listed once, and its rows are the equations `H_p(ρ_Y) = 𝒩^±(z)` for all `p ∈ 𝒫` and residue vectors `ρ_Y`. -/
structure SystemEncodes (sys : SysReq) (π : List Bool) (s : Bool) (z : Fin C.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (C.J + 1) → ℤ) : Prop where
  nodup : sys.pts.Nodup
  mem_pts : ∀ u, u ∈ sys.pts ↔ ∃ y ∈ C.box z δ, pointList y = u
  rows_sound : ∀ row ∈ sys.rows, ∃ p ∈ C.primes, ∃ ρY ∈ C.residueVectors z p,
    row = systemRow C (splitWeight C π s) z σ δ p ρY
  rows_complete : ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
    systemRow C (splitWeight C π s) z σ δ p ρY ∈ sys.rows

/-- The value at the point `0` returned by an exact solver (`v = H̃(0)`, Step 3 of `sec:algorithm`), and `0` if the
solver reports an inconsistent system. -/
noncomputable def solvedValue (S : SolveMachine) (sys : SysReq) : ℚ :=
  match S.solve sys with
  | some F => pointValue sys.pts F [0, 0]
  | none => 0

theorem residueVectors_nonneg {z : Fin C.ncol} {p : ℕ} {ρY : Fin 2 → ℤ} (hρ : ρY ∈ C.residueVectors z p)
    (j : Fin 2) : 0 ≤ ρY j := by
  unfold Algorithm.CellCall.residueVectors at hρ
  rw [Fintype.mem_piFinset] at hρ
  have h := hρ j
  split at h
  · exact (Finset.mem_Ico.mp h).1
  · rw [Finset.mem_singleton.mp h]

/-- The base residue-class test of a row is the congruence of the point to `ρ_Y`. -/
theorem inClass_pointList (p : ℕ) (ρY : Fin 2 → ℤ) (h0 : ∀ j, 0 ≤ ρY j) (y : Fin 2 → ℤ) :
    inClass p [(ρY 0).toNat, (ρY 1).toNat] (pointList y) = true ↔ ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)] := by
  have e0 : ((ρY 0).toNat : ℤ) = ρY 0 := Int.toNat_of_nonneg (h0 0)
  have e1 : ((ρY 1).toNat : ℤ) = ρY 1 := Int.toNat_of_nonneg (h0 1)
  simp only [inClass, pointList, List.length_cons, List.length_nil, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Fin.forall_fin_two, Int.ModEq]
  constructor
  · intro h
    have a := h 0 (by norm_num)
    have b := h 1 (by norm_num)
    simp only [List.getD_cons_zero, List.getD_cons_succ, e0, e1] at a b
    exact ⟨a, b⟩
  · rintro ⟨a, b⟩ i hi
    interval_cases i
    · simpa [e0] using a
    · simpa [e1] using b

/-- Reindexing a sum over the listed points of an encoding system as a sum over the box. -/
theorem sum_pts_eq_sum_box {sys : SysReq} {z : Fin C.ncol} {δ : Fin 2 → Fin (C.J + 1) → ℤ}
    (hmem : ∀ u, u ∈ sys.pts ↔ ∃ y ∈ C.box z δ, pointList y = u) (P : List ℤ → Bool) (φ : List ℤ → ℚ) :
    ∑ u ∈ sys.pts.toFinset.filter (fun u => P u = true), φ u =
      ∑ y ∈ (C.box z δ).filter (fun y => P (pointList y) = true), φ (pointList y) := by
  classical
  have himg : sys.pts.toFinset = (C.box z δ).image pointList := by
    ext u
    rw [List.mem_toFinset, hmem u, Finset.mem_image]
  rw [himg, Finset.filter_image, Finset.sum_image]
  intro a _ b _ h
  exact pointList_injective h

/-- **The exact solver returns `v^±_{z,σ,δ}`** (Step 3, paper/paper.tex, with step (1) of the proof
of `prop:sound`): on a certified column, for `κ_σ ≠ 0`, a digit vector `δ` and a prefix of length
at most `S`, every `SolveMachine` applied to a system encoding the system of the part `s` of the weights returns a
solution, whose value at `0` is `v^±_{z,σ,δ} = H^±(0)`. -/
theorem solvedValue_eq (S : SolveMachine) (sys : SysReq) (H : C.ReconstructionHypotheses) (π : List Bool)
    (hπ : π.length ≤ C.seedLength) (s : Bool) (z : Fin C.ncol) (hz : z ∈ C.certifiedColumns)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z) (henc : SystemEncodes C sys π s z σ δ) :
    solvedValue S sys = (splitValue C π s z σ δ : ℚ) := by
  classical
  have hcert : C.Certified z := by
    unfold Algorithm.CellCall.certifiedColumns at hz
    exact (Finset.mem_filter.mp hz).2
  set Fstar : (Fin 2 → ℤ) → ℚ := fun y => (classValueOf C (splitWeight C π s) z σ δ y : ℚ) with hFstar
  obtain ⟨hs1, hs2⟩ := classValueOf_solves C H π hπ s z hcert σ hσ δ hδ
  have hnonneg : ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
      0 ≤ recoveredCountOf C (splitWeight C π s) z σ p δ ρY :=
    fun p hp ρY hρ => recoveredCountOf_nonneg C H π hπ s z hcert σ hσ δ hδ p hp ρY hρ
  -- the class value at a listed point
  let vecOf : List ℤ → (Fin 2 → ℤ) := fun u j => u.getD j.val 0
  have hvec : ∀ y, vecOf (pointList y) = y := by
    intro y
    funext j
    fin_cases j <;> rfl
  -- the row sum of a solution, reindexed over the box
  have hrow : ∀ (F : List ℚ), F.length = sys.pts.length → ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
      (((sys.pts.zip F).filter fun uf => inClass p [(ρY 0).toNat, (ρY 1).toNat] uf.1).map Prod.snd).sum =
        ∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]),
          pointValue sys.pts F (pointList y) := by
    intro F hF p _ ρY hρ
    rw [sum_filter_zip _ sys.pts F henc.nodup hF, sum_pts_eq_sum_box C henc.mem_pts]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp only [Finset.mem_filter]
    rw [inClass_pointList p ρY (residueVectors_nonneg C hρ) y]
  -- the class function, listed over the points, solves the system
  have hsolve0 : SysSolves sys (sys.pts.map fun u => Fstar (vecOf u)) := by
    refine ⟨by simp, fun row hrowmem => ?_⟩
    obtain ⟨p, hp, ρY, hρ, rfl⟩ := henc.rows_sound row hrowmem
    simp only [systemRow]
    rw [hrow _ (by simp) p hp ρY hρ]
    have hcongr : ∀ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]),
        pointValue sys.pts (sys.pts.map fun u => Fstar (vecOf u)) (pointList y) = Fstar y := by
      intro y hy
      have hy' : pointList y ∈ sys.pts := (henc.mem_pts _).mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩
      rw [pointValue_map _ sys.pts henc.nodup _ hy', hvec]
    rw [Finset.sum_congr rfl hcongr]
    simp only [hFstar]
    rw [← Int.cast_sum, hs2 p hp ρY hρ, natCast_toNat (hnonneg p hp ρY hρ)]
  -- the solver returns a solution
  cases hsol : S.solve sys with
  | none => exact absurd hsolve0 (S.complete sys hsol _)
  | some F =>
    have hF := S.sound sys F hsol
    have hlen : F.length = sys.pts.length := hF.1
    -- the solution, as a function on `ℤ²`, is the class function
    have hfun : ∀ y, (if y ∈ C.box z δ then pointValue sys.pts F (pointList y) else 0) = Fstar y := by
      intro y
      refine splitSolution_unique C H π hπ s z hz σ hσ δ hδ
        (fun y => if y ∈ C.box z δ then pointValue sys.pts F (pointList y) else 0)
        (fun y hy => by simp only [if_neg hy]) ?_ y
      intro p hp ρY hρ
      have hsum := hF.2 _ (henc.rows_complete p hp ρY hρ)
      simp only [systemRow] at hsum
      rw [hrow F hlen p hp ρY hρ] at hsum
      rw [Finset.sum_congr rfl fun y hy => if_pos (Finset.mem_filter.mp hy).1, hsum,
        natCast_toNat (hnonneg p hp ρY hρ)]
    unfold solvedValue
    rw [hsol]
    dsimp only
    unfold splitValue
    by_cases h0 : (0 : Fin 2 → ℤ) ∈ C.box z δ
    · have := hfun 0
      rw [if_pos h0] at this
      exact this
    · have hnot : [0, 0] ∉ sys.pts := by
        intro hm
        obtain ⟨y, hy, hyu⟩ := (henc.mem_pts _).mp hm
        have : y = 0 := pointList_injective (by rw [hyu]; rfl)
        exact h0 (this ▸ hy)
      rw [pointValue_of_not_mem _ _ _ hnot, classValueOf_support C H _ z hcert σ hσ δ 0 h0, Int.cast_zero]

end Encoding

/-- **The child objective from the exact solver** (Step 3, `sec:algorithm`, paper/paper.tex): for every child
evaluation, every `SolveMachine` and every choice of base systems encoding the systems of the two parts of the
weights,
`Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ (v⁺_{z,σ,δ} - v⁻_{z,σ,δ})` with the values returned by the solver. -/
theorem childObjective_solved {B1 B2 : ℕ} (S : SolveMachine) (q : ChildRequest B1 B2)
    (sys : Bool → Fin q.cellCall.ncol → Cycle.SignPattern Algorithm.traceOrder →
      (Fin 2 → Fin (q.cellCall.J + 1) → ℤ) → SysReq)
    (henc : ∀ s, ∀ z ∈ q.cellCall.certifiedColumns, ∀ σ, Cycle.kappa Algorithm.traceOrder σ ≠ 0 →
      ∀ δ ∈ q.cellCall.digitVectors z, SystemEncodes q.cellCall (sys s z σ δ) q.seedPrefix s z σ δ) :
    (childObjective q : ℚ) = ∑ z ∈ q.cellCall.certifiedColumns, ∑ σ : Cycle.SignPattern Algorithm.traceOrder,
      (Cycle.kappa Algorithm.traceOrder σ : ℚ) * ∑ δ ∈ q.cellCall.digitVectors z,
        (solvedValue S (sys true z σ δ) - solvedValue S (sys false z σ δ)) := by
  have H : q.cellCall.ReconstructionHypotheses := reconstructionHypotheses_of_dispatch q.dispatched q.witness
  rw [childObjective_split]
  push_cast
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : Cycle.kappa Algorithm.traceOrder σ = 0
  · simp [hσ]
  · congr 1
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [solvedValue_eq _ S _ H _ q.prefix_le true z hz σ hσ δ hδ (henc true z hz σ hσ δ hδ),
      solvedValue_eq _ S _ H _ q.prefix_le false z hz σ hσ δ hδ (henc false z hz σ hσ δ hδ)]

end NearQuarticWires.Greedy
