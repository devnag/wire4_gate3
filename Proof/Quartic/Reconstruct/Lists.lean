import Proof.Quartic.Reconstruct.Schedule

/-!
# The loops of the reconstruction stage as lists

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The reconstruction stage of a child evaluation runs its loops in a fixed order (`Schedule`): the part `s`, the
pattern `σ`, the digit vector `δ`, then the prime `p` and the residue vector `ρ_Y` for the printed tables
(`printList`), or the certified column `z` for the exact systems (`systemList`). This file lists these loops:

* `vecList L k`: all vectors of length `k` with entries in the list `L`, the first entry outermost;
* `patternList`: the `4^m` patterns `σ`; `digitList`: the digit vectors (`mem_digitList`); `residueListOf`: the
  residue vectors modulo `p`; `certList`: the certified columns `Z_c` in increasing order;
* `printList`: the tables `(s, σ, δ, p, ρ_Y)` as print requests, at most `tableCount` (`printList_length_le`);
* `activePatterns`: the patterns with `κ_σ ≠ 0`;
* `systemList`: the systems `(s, σ, δ, z)` with `κ_σ ≠ 0` and `z ∈ Z_c`, at most `systemCount`
  (`systemList_length_le`).

The value of a system is read off the solver's answer at the position of the point `0` in the list of points
(`solvedRead`, equal to `Greedy.solvedValue`: `solvedRead_eq`). **`childObjective_eq_systemList`**: the child
objective is the sum, over `systemList`, of the coefficient `(±1)κ_σ` (`systemCoef`) times the numerator of the
value read off the solver: this is the arithmetic of the last step of the stage.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open Finset
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces.Formats (SysReq SolveMachine)

variable {B1 B2 : ℕ}

/-! ## Lists and sums -/

theorem sum_map_flatMap {α β : Type} (L : List α) (g : α → List β) (f : β → ℤ) :
    ((L.flatMap g).map f).sum = (L.map fun a => ((g a).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- The sum over a list without repetitions is the sum over the finite set of its entries. -/
theorem listSum_eq_finsetSum {α : Type} [DecidableEq α] (L : List α) (s : Finset α) (hL : L.Nodup)
    (hmem : ∀ x, x ∈ L ↔ x ∈ s) (f : α → ℤ) : (L.map f).sum = ∑ x ∈ s, f x := by
  rw [← List.sum_toFinset f hL]
  congr 1
  ext x
  rw [List.mem_toFinset, hmem]

/-! ## Vectors -/

/-- All vectors of length `k` with entries in `L`, the first entry outermost. -/
def vecList {α : Type} (L : List α) : (k : ℕ) → List (Fin k → α)
  | 0 => [Fin.elim0]
  | k + 1 => (L ×ˢ vecList L k).map fun p => Fin.cons p.1 p.2

theorem mem_vecList {α : Type} (L : List α) : ∀ (k : ℕ) (v : Fin k → α), v ∈ vecList L k ↔ ∀ i, v i ∈ L
  | 0, v => by
    simp only [vecList, List.mem_singleton]
    exact ⟨fun _ i => i.elim0, fun _ => funext fun i => i.elim0⟩
  | k + 1, v => by
    show v ∈ (L ×ˢ vecList L k).map (fun p => Fin.cons p.1 p.2) ↔ _
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨a, w⟩, hab, rfl⟩ i
      rw [List.mem_product] at hab
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hab.1
      · simpa using (mem_vecList L k w).mp hab.2 i
    · intro h
      exact ⟨(v 0, Fin.tail v), List.mem_product.mpr ⟨h 0, (mem_vecList L k _).mpr fun i => h i.succ⟩,
        Fin.cons_self_tail v⟩

theorem vecList_nodup {α : Type} (L : List α) (hL : L.Nodup) : ∀ k, (vecList L k).Nodup
  | 0 => List.nodup_singleton _
  | k + 1 => by
    refine List.Nodup.map (fun p p' h => ?_) (hL.product (vecList_nodup L hL k))
    have h1 : p.1 = p'.1 := by simpa using congrFun h 0
    have h2 : p.2 = p'.2 := funext fun i => by simpa using congrFun h i.succ
    exact Prod.ext h1 h2

/-! ## The loops -/

/-- The `4^m` patterns `σ` (`lem:cycle`). -/
def patternList : List (Cycle.SignPattern Algorithm.traceOrder) := vecList [false, true] (2 * Algorithm.traceOrder)

theorem mem_patternList (σ : Cycle.SignPattern Algorithm.traceOrder) : σ ∈ patternList :=
  (mem_vecList _ _ σ).mpr fun i => by cases σ i <;> simp

theorem patternList_nodup : patternList.Nodup := vecList_nodup _ (by simp) _

/-- The patterns with `κ_σ ≠ 0`, the only ones that enter `Ψ̃(π)` (Step 3 of `sec:algorithm`). -/
def activePatterns : List (Cycle.SignPattern Algorithm.traceOrder) :=
  patternList.filter fun σ => decide (Cycle.kappa Algorithm.traceOrder σ ≠ 0)

theorem mem_activePatterns (σ : Cycle.SignPattern Algorithm.traceOrder) :
    σ ∈ activePatterns ↔ Cycle.kappa Algorithm.traceOrder σ ≠ 0 := by
  unfold activePatterns
  simp [mem_patternList]

theorem activePatterns_nodup : activePatterns.Nodup := patternList_nodup.filter _

section Child

variable (q : ChildRequest B1 B2)

/-- The digit vectors of circuit `j` (Step 3 of `sec:algorithm`): all vectors with entries in `(-h_E, h_E)` for a
circuit `j ∈ 𝒥`, and the zero vector otherwise. -/
noncomputable def digitAxisList (j : Fin 2) : List (Fin (q.cellCall.J + 1) → ℤ) := by
  classical
  exact if j ∈ Builder.circuitSet q.call then
      vecList (intervalList (-(q.selected.1.hE : ℤ) + 1) ((q.selected.1.hE : ℤ) - 1)) (q.cellCall.J + 1)
    else [0]

/-- The digit vectors `δ`, the first circuit outermost. -/
noncomputable def digitList : List (Fin 2 → Fin (q.cellCall.J + 1) → ℤ) :=
  (digitAxisList q 0 ×ˢ digitAxisList q 1).map fun ab => ![ab.1, ab.2]

theorem mem_digitAxisList (j : Fin 2) (v : Fin (q.cellCall.J + 1) → ℤ) :
    v ∈ digitAxisList q j ↔ v ∈ (if j ∈ Builder.circuitSet q.call then
      Fintype.piFinset fun _ => Finset.Ioo (-(q.selected.1.hE : ℤ)) q.selected.1.hE else
        ({0} : Finset (Fin (q.cellCall.J + 1) → ℤ))) := by
  unfold digitAxisList
  split
  · rw [mem_vecList, Fintype.mem_piFinset]
    refine forall_congr' fun i => ?_
    rw [mem_intervalList, Finset.mem_Ioo]
    omega
  · simp

theorem digitAxisList_nodup (j : Fin 2) : (digitAxisList q j).Nodup := by
  unfold digitAxisList
  split
  · exact vecList_nodup _ (intervalList_nodup _ _) _
  · exact List.nodup_singleton _

theorem mem_digitList (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) : δ ∈ digitList q ↔ δ ∈ digitSet q := by
  classical
  unfold digitList digitSet
  rw [List.mem_map, Fintype.mem_piFinset]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [List.mem_product] at hab
    intro j
    fin_cases j
    · exact (mem_digitAxisList q 0 a).mp hab.1
    · exact (mem_digitAxisList q 1 b).mp hab.2
  · intro h
    refine ⟨(δ 0, δ 1), List.mem_product.mpr ⟨(mem_digitAxisList q 0 _).mpr (h 0),
      (mem_digitAxisList q 1 _).mpr (h 1)⟩, ?_⟩
    funext j
    fin_cases j <;> rfl

theorem digitList_nodup : (digitList q).Nodup := by
  refine List.Nodup.map (fun a b h => ?_) ((digitAxisList_nodup q 0).product (digitAxisList_nodup q 1))
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

/-- The residue vectors `ρ_Y` modulo `p` of a child (Step 3 of `sec:algorithm`), the first circuit outermost. -/
noncomputable def residueListOf (p : ℕ) : List (Fin 2 → ℤ) := by
  classical
  exact ((if (0 : Fin 2) ∈ Builder.circuitSet q.call then (List.range p).map Int.ofNat else [0]) ×ˢ
    (if (1 : Fin 2) ∈ Builder.circuitSet q.call then (List.range p).map Int.ofNat else [0])).map
      fun ab => ![ab.1, ab.2]

/-- The certified columns `Z_c` in increasing order. -/
noncomputable def certList : List (Fin q.cellCall.ncol) := by
  classical
  exact (List.finRange q.cellCall.ncol).filter fun z => decide (z ∈ q.cellCall.certifiedColumns)

theorem mem_certList (z : Fin q.cellCall.ncol) : z ∈ certList q ↔ z ∈ q.cellCall.certifiedColumns := by
  classical
  unfold certList
  simp

theorem certList_nodup : (certList q).Nodup := by
  classical
  unfold certList
  exact (List.nodup_finRange _).filter _

/-- The print request `(s, σ, p, δ, ρ_Y)` of a child, for a prime `p` of the list of `𝒫`. -/
noncomputable def printRequestOf (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (p : {p // p ∈ primeList q.cellCall}) (ρ : Fin 2 → ℤ) :
    PrintRequest B1 B2 where
  child := q
  sign := s
  pattern := σ
  prime := p.1
  prime_mem := (mem_primeList _ _).mp p.2
  digits := δ
  residues := ρ

/-- **The printed tables** of a child (Step 3 of `sec:algorithm`): for each part `s`, pattern `σ`, digit vector `δ`,
prime `p ∈ 𝒫` (increasing) and residue vector `ρ_Y` modulo `p`, the print request `(s, σ, p, δ, ρ_Y)`. -/
noncomputable def printList : List (PrintRequest B1 B2) :=
  [true, false].flatMap fun s => patternList.flatMap fun σ => (digitList q).flatMap fun δ =>
    (primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ => printRequestOf q s σ δ p ρ

/-- The index of a system: the part, the pattern, the digit vector and the column. -/
abbrev SystemIndex (q : ChildRequest B1 B2) : Type :=
  Bool × Cycle.SignPattern Algorithm.traceOrder × (Fin 2 → Fin (q.cellCall.J + 1) → ℤ) × Fin q.cellCall.ncol

/-- **The exact systems** of a child (Step 3 of `sec:algorithm`): for each part `s`, pattern `σ` with `κ_σ ≠ 0`,
digit vector `δ` and certified column `z ∈ Z_c` (increasing), the index `(s, σ, δ, z)`. -/
noncomputable def systemList : List (SystemIndex q) :=
  [true, false].flatMap fun s => activePatterns.flatMap fun σ => (digitList q).flatMap fun δ =>
    (certList q).map fun z => (s, σ, δ, z)

/-- The listed system of an index. -/
noncomputable def systemAt (x : SystemIndex q) : SysReq :=
  systemOf q.cellCall q.seedPrefix x.1 x.2.2.2 x.2.1 x.2.2.1

/-- The coefficient `(±1)κ_σ` of a system in `Ψ̃(π)`. -/
def systemCoef (x : SystemIndex q) : ℤ := partSign x.1 * Cycle.kappa Algorithm.traceOrder x.2.1

end Child

/-! ## The value at the point `0` -/

/-- The value at the point `0` read off the solver's answer: the entry at the position of `[0, 0]` in the list of
points (the entry is absent, hence `0`, when `0` is not a point), and `0` when the solver reports an inconsistent
system. -/
noncomputable def solvedRead (S : SolveMachine) (sys : SysReq) : ℚ :=
  match S.solve sys with
  | some F => F.getD (sys.pts.idxOf [0, 0]) 0
  | none => 0

theorem pointValue_eq_getD (u : List ℤ) :
    ∀ (pts : List (List ℤ)) (F : List ℚ), pts.Nodup → F.length = pts.length →
      pointValue pts F u = F.getD (pts.idxOf u) 0
  | [], [], _, _ => by simp [pointValue]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, f :: fs, hnd, hl => by
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    rw [pointValue_cons]
    by_cases h : a = u
    · subst h
      rw [if_pos rfl, pointValue_of_not_mem as fs a ha, add_zero, List.idxOf_cons_self]
      rfl
    · rw [if_neg h, zero_add, List.idxOf_cons_ne _ h]
      exact pointValue_eq_getD u as fs (List.nodup_cons.mp hnd).2 (by simpa using hl)

/-- On a system with distinct points, the value read at the position of `0` is `Greedy.solvedValue`. -/
theorem solvedRead_eq (S : SolveMachine) (sys : SysReq) (hnd : sys.pts.Nodup) :
    solvedRead S sys = solvedValue S sys := by
  unfold solvedRead solvedValue
  cases h : S.solve sys with
  | none => rfl
  | some F =>
    exact (pointValue_eq_getD [0, 0] sys.pts F hnd (S.sound sys F h).1).symm

/-! ## The child objective over the listed systems -/

/-- **The child objective over the listed systems** (Step 3, `sec:algorithm`, paper/paper.tex): for every child
evaluation and every exact solver, `Ψ̃(π)` is the sum over `systemList` of the coefficient `(±1)κ_σ` times the
numerator of the value read off the solver at the point `0`. -/
theorem childObjective_eq_systemList (S : SolveMachine) (q : ChildRequest B1 B2) :
    childObjective q =
      ((systemList q).map fun x => systemCoef q x * (solvedRead S (systemAt q x)).num).sum := by
  classical
  rw [childObjective_eq_schedule S q]
  unfold systemList
  rw [sum_map_flatMap, listSum_eq_finsetSum _ Finset.univ (by simp) (by simp)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_map_flatMap, listSum_eq_finsetSum _
    (Finset.univ.filter fun σ => Cycle.kappa Algorithm.traceOrder σ ≠ 0) activePatterns_nodup
    (fun σ => by simp [mem_activePatterns]), Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hk : Cycle.kappa Algorithm.traceOrder σ = 0
  · rw [if_neg (not_not.mpr hk)]
    simp [hk]
  rw [if_pos hk]
  rw [sum_map_flatMap, listSum_eq_finsetSum _ (digitSet q) (digitList_nodup q) (mem_digitList q)]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [List.map_map, listSum_eq_finsetSum _ q.cellCall.certifiedColumns (certList_nodup q) (mem_certList q)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Function.comp, systemCoef, systemAt, solvedNum]
  rw [solvedRead_eq S _ (boxPoints_nodup _ z δ)]

/-! ## The lengths of the loops (`prop:time`) -/

theorem length_flatMap_le {α β : Type} (L : List α) (g : α → List β) (B : ℕ) (h : ∀ a ∈ L, (g a).length ≤ B) :
    (L.flatMap g).length ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    nlinarith

theorem vecList_length {α : Type} (L : List α) : ∀ k, (vecList L k).length = L.length ^ k
  | 0 => rfl
  | k + 1 => by
    show ((L ×ˢ vecList L k).map _).length = _
    rw [List.length_map, List.length_product, vecList_length L k, pow_succ, mul_comm]

theorem patternList_length : patternList.length = 4 ^ Algorithm.traceOrder := by
  unfold patternList
  rw [vecList_length]
  norm_num

theorem digitList_length (q : ChildRequest B1 B2) : (digitList q).length = (digitSet q).card := by
  classical
  rw [← List.toFinset_card_of_nodup (digitList_nodup q)]
  congr 1
  ext δ
  rw [List.mem_toFinset, mem_digitList]

theorem residueListOf_length_le (q : ChildRequest B1 B2) {p : ℕ} (hp : 1 ≤ p) :
    (residueListOf q p).length ≤ p ^ 2 := by
  classical
  unfold residueListOf
  rw [List.length_map, List.length_product, pow_two]
  apply Nat.mul_le_mul
  · split <;> simp [hp]
  · split <;> simp [hp]

/-- **At most `tableCount` printed tables** (`prop:time`). -/
theorem printList_length_le (q : ChildRequest B1 B2) : (printList q).length ≤ tableCount q := by
  have hD := card_digitSet_le q
  have hinner : ∀ (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ),
      ((primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ =>
        printRequestOf q s σ δ p ρ).length ≤ q.selected.1.P ^ 3 := by
    intro s σ δ
    refine (length_flatMap_le _ _ (q.selected.1.P ^ 2) fun p _ => ?_).trans ?_
    · have hp' := (mem_primeList _ p.1).mp p.2
      rw [List.length_map]
      exact (residueListOf_length_le q (one_le_of_mem_primes q hp')).trans
        (Nat.pow_le_pow_left (le_P_of_mem_primes q hp') 2)
    · rw [List.length_attach]
      unfold primeList
      rw [Finset.length_sort, pow_succ' _ 2]
      exact Nat.mul_le_mul_right _ (card_primes_le q)
  have hδ : ∀ (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder), ((digitList q).flatMap fun δ =>
      (primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ =>
        printRequestOf q s σ δ p ρ).length ≤ (digitList q).length * q.selected.1.P ^ 3 :=
    fun s σ => length_flatMap_le _ _ _ fun δ _ => hinner s σ δ
  have hσ : ∀ s : Bool, (patternList.flatMap fun σ => (digitList q).flatMap fun δ =>
      (primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ =>
        printRequestOf q s σ δ p ρ).length ≤ patternList.length * ((digitList q).length * q.selected.1.P ^ 3) :=
    fun s => length_flatMap_le _ _ _ fun σ _ => hδ s σ
  have htot := length_flatMap_le [true, false] _ _ fun s _ => hσ s
  unfold printList
  refine htot.trans ?_
  rw [patternList_length, digitList_length]
  unfold tableCount
  calc [true, false].length * (4 ^ Algorithm.traceOrder * ((digitSet q).card * q.selected.1.P ^ 3))
      ≤ 2 * (4 ^ Algorithm.traceOrder * (q.selected.1.P ^ (2 * (q.cellCall.J + 1)) * q.selected.1.P ^ 3)) := by
        simp only [List.length_cons, List.length_nil]
        gcongr
    _ = _ := by rw [pow_add]; ring

/-- **At most `systemCount` exact systems** (`prop:time`). -/
theorem systemList_length_le (q : ChildRequest B1 B2) : (systemList q).length ≤ systemCount q := by
  classical
  have hD := card_digitSet_le q
  have hc : (certList q).length ≤ q.cellCall.ncol := by
    unfold certList
    exact (List.length_filter_le _ _).trans (by simp)
  have hδ : ∀ (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder),
      ((digitList q).flatMap fun δ => (certList q).map fun z => ((s, σ, δ, z) : SystemIndex q)).length ≤
        (digitList q).length * q.cellCall.ncol :=
    fun s σ => length_flatMap_le _ _ _ fun δ _ => by rw [List.length_map]; exact hc
  have hσ : ∀ s : Bool, (activePatterns.flatMap fun σ => (digitList q).flatMap fun δ =>
      (certList q).map fun z => ((s, σ, δ, z) : SystemIndex q)).length ≤
        patternList.length * ((digitList q).length * q.cellCall.ncol) := fun s =>
    (length_flatMap_le _ _ _ fun σ _ => hδ s σ).trans
      (Nat.mul_le_mul_right _ (List.length_filter_le _ _))
  have htot := length_flatMap_le [true, false] _ _ fun s _ => hσ s
  unfold systemList
  refine htot.trans ?_
  rw [patternList_length, digitList_length]
  unfold systemCount
  calc [true, false].length * (4 ^ Algorithm.traceOrder * ((digitSet q).card * q.cellCall.ncol))
      ≤ 2 * (4 ^ Algorithm.traceOrder * (q.selected.1.P ^ (2 * (q.cellCall.J + 1)) * q.cellCall.ncol)) := by
        simp only [List.length_cons, List.length_nil]
        gcongr
    _ = _ := by ring

end NearQuarticWires.Reconstruct
