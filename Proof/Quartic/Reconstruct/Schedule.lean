import Proof.Quartic.Reconstruct.Systems

/-!
# The schedule of the reconstruction stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

On a child evaluation, the data that shape the exact systems are the same on every column: the set `𝒥` of circuits
of the call, `h_E`, `M_1`, `A`, `Λ`, the rates and the occurrence counts `G_j` are parameters of the call
(`Builder.columnData`). Hence the digit vectors (`digitSet`), the residue vectors (`residueSet`) and the boxes are
the same for all columns, and only the right sides of the systems (the printed counts `𝒩(z)`) depend on `z`.

The reconstruction stage therefore runs the loops in the order

  part `s`, pattern `σ`, digit vector `δ` (one group of tables per `(s, σ, δ)`), then columns `z`,

and `childObjective_eq_schedule` writes the child objective in this order:
`Ψ̃(π) = Σ_s Σ_σ Σ_{δ} Σ_{z ∈ Z_c} (±1) κ_σ v^s_{z,σ,δ}`.

The counts of `prop:time`: the tables of a child are indexed by `(s, σ, δ, p, ρ_Y)`
(`tableIndices`), at most `tableCount`; the systems by `(s, σ, δ, z)`, at most `systemCount`; each system has at most
`rowCount = P^3` rows. They follow from `h_E = ⌊P/4⌋` (so `2h_E - 1 < P`) and `𝒫 ⊆ [1, P]` (`sec:params`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open Finset
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces.Formats (SysReq SolveMachine)

variable {B1 B2 : ℕ}

/-! ## The column data are parameters of the call -/

section Global

variable (q : ChildRequest B1 B2)

/-- The rules of `sec:params` satisfied by the parameters of a child evaluation. -/
theorem rules : Cells.ParameterRules (Builder.callInput q.call) q.selected.1 :=
  Cells.prepare_spec _ q.selected.1 q.selected.2

/-- `sec:cells`: the circuits of every column are the circuits `𝒥` of the call. -/
theorem column_circuits (z : Fin q.cellCall.ncol) : (q.cellCall.column z).circuits = Builder.circuitSet q.call :=
  rfl

/-- The digit vectors `δ = (δ^{(j)})_{j ∈ 𝒥}` with entries in `(-h_E, h_E)` (Step 3 of `sec:algorithm`); circuits
outside `𝒥` carry the zero vector. -/
noncomputable def digitSet : Finset (Fin 2 → Fin (q.cellCall.J + 1) → ℤ) := by
  classical
  exact Fintype.piFinset fun j =>
    if j ∈ Builder.circuitSet q.call then
      Fintype.piFinset fun _ => Finset.Ioo (-(q.selected.1.hE : ℤ)) q.selected.1.hE
    else {0}

/-- The digit vectors are the same on every column. -/
theorem digitVectors_eq (z : Fin q.cellCall.ncol) : q.cellCall.digitVectors z = digitSet q := rfl

/-- The residue vectors `ρ_Y ∈ (ℤ/p)^{𝒥}` as representatives in `[0, p)` (Step 3 of `sec:algorithm`). -/
noncomputable def residueSet (p : ℕ) : Finset (Fin 2 → ℤ) := by
  classical
  exact Fintype.piFinset fun j => if j ∈ Builder.circuitSet q.call then Finset.Ico (0 : ℤ) p else {0}

/-- The residue vectors are the same on every column. -/
theorem residueVectors_eq (z : Fin q.cellCall.ncol) (p : ℕ) : q.cellCall.residueVectors z p = residueSet q p := rfl

end Global

/-! ## The child objective in the order of the loops -/

/-- The sign of a part of the weights: `+1` for the positive part, `-1` for the negative part. -/
def partSign (s : Bool) : ℤ := if s then 1 else -1

/-- **The child objective in the order of the loops** (Step 3, `sec:algorithm`, paper/paper.tex): for every exact
solver,
`Ψ̃(π) = Σ_s Σ_σ Σ_{δ} Σ_{z ∈ Z_c} (±1) κ_σ v^s_{z,σ,δ}`, where `v^s` is the numerator of the value at `0` returned
by the solver on the listed system of the part `s` (`systemOf`). -/
theorem childObjective_eq_schedule (S : SolveMachine) (q : ChildRequest B1 B2) :
    childObjective q = ∑ s : Bool, ∑ σ : Cycle.SignPattern Algorithm.traceOrder, ∑ δ ∈ digitSet q,
      ∑ z ∈ q.cellCall.certifiedColumns,
        partSign s * Cycle.kappa Algorithm.traceOrder σ * solvedNum S (systemOf q.cellCall q.seedPrefix s z σ δ) := by
  set F : Bool → Fin q.cellCall.ncol → Cycle.SignPattern Algorithm.traceOrder →
      (Fin 2 → Fin (q.cellCall.J + 1) → ℤ) → ℤ :=
    fun s z σ δ => partSign s * Cycle.kappa Algorithm.traceOrder σ *
      solvedNum S (systemOf q.cellCall q.seedPrefix s z σ δ) with hF
  rw [childObjective_eq_solvedNum S q]
  calc ∑ z ∈ q.cellCall.certifiedColumns, ∑ σ : Cycle.SignPattern Algorithm.traceOrder,
        Cycle.kappa Algorithm.traceOrder σ * ∑ δ ∈ q.cellCall.digitVectors z,
          (solvedNum S (systemOf q.cellCall q.seedPrefix true z σ δ) -
            solvedNum S (systemOf q.cellCall q.seedPrefix false z σ δ))
      = ∑ z ∈ q.cellCall.certifiedColumns, ∑ σ : Cycle.SignPattern Algorithm.traceOrder,
          ∑ δ ∈ digitSet q, ∑ s : Bool, F s z σ δ := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun σ _ => ?_
        rw [digitVectors_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Fintype.sum_bool]
        simp only [hF, partSign, if_true, Bool.false_eq_true, if_false]
        ring
    _ = ∑ s : Bool, ∑ σ : Cycle.SignPattern Algorithm.traceOrder, ∑ δ ∈ digitSet q,
          ∑ z ∈ q.cellCall.certifiedColumns, F s z σ δ := by
        -- move `s` outermost, then `z` innermost
        have h1 : ∀ z, ∑ σ : Cycle.SignPattern Algorithm.traceOrder, ∑ δ ∈ digitSet q, ∑ s : Bool, F s z σ δ =
            ∑ s : Bool, ∑ σ : Cycle.SignPattern Algorithm.traceOrder, ∑ δ ∈ digitSet q, F s z σ δ := fun z =>
          (Finset.sum_congr rfl fun σ _ => Finset.sum_comm).trans Finset.sum_comm
        have h3 : ∀ s, ∑ z ∈ q.cellCall.certifiedColumns, ∑ σ : Cycle.SignPattern Algorithm.traceOrder,
            ∑ δ ∈ digitSet q, F s z σ δ =
            ∑ σ : Cycle.SignPattern Algorithm.traceOrder, ∑ δ ∈ digitSet q,
              ∑ z ∈ q.cellCall.certifiedColumns, F s z σ δ := fun s =>
          Finset.sum_comm.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_comm)
        exact ((Finset.sum_congr rfl fun z _ => h1 z).trans Finset.sum_comm).trans
          (Finset.sum_congr rfl fun s _ => h3 s)

/-! ## The counts of `prop:time` -/

section Counts

variable (q : ChildRequest B1 B2)

theorem hE_mul_four_le : 4 * q.selected.1.hE ≤ q.selected.1.P := by
  rw [(rules q).hE_eq]
  exact Nat.mul_div_le _ 4

theorem one_le_P : 1 ≤ q.selected.1.P := by
  have := (rules q).prime_candidate.1
  omega

theorem le_P_of_mem_primes {p : ℕ} (hp : p ∈ q.cellCall.primes) : p ≤ q.selected.1.P := by
  have h : p ∈ q.selected.1.primes := hp
  rw [(rules q).primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at h
  exact h.1

theorem card_primes_le : q.cellCall.primes.card ≤ q.selected.1.P := by
  have hsub : q.cellCall.primes ⊆ Finset.Icc 1 q.selected.1.P := by
    intro p hp
    have h : p ∈ q.selected.1.primes := hp
    rw [(rules q).primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at h
    exact Finset.mem_Icc.mpr ⟨h.2.1.one_lt.le, h.1⟩
  simpa using Finset.card_le_card hsub

/-- `#{δ} ≤ P^{2(J+1)}`: each of the at most two circuits has `J + 1` digits in `(-h_E, h_E)`, and `2h_E - 1 < P`. -/
theorem card_digitSet_le : (digitSet q).card ≤ q.selected.1.P ^ (2 * (q.cellCall.J + 1)) := by
  classical
  have hP := one_le_P q
  have hE := hE_mul_four_le q
  have hcoord : ∀ j : Fin 2, ((if j ∈ Builder.circuitSet q.call then
      Fintype.piFinset fun _ : Fin (q.cellCall.J + 1) => Finset.Ioo (-(q.selected.1.hE : ℤ)) q.selected.1.hE
      else {0}) : Finset (Fin (q.cellCall.J + 1) → ℤ)).card ≤ q.selected.1.P ^ (q.cellCall.J + 1) := by
    intro j
    split
    · rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Ioo]
      apply Nat.pow_le_pow_left
      omega
    · rw [Finset.card_singleton]
      exact Nat.one_le_pow _ _ (by omega)
  unfold digitSet
  rw [Fintype.card_piFinset, Fin.prod_univ_two, show 2 * (q.cellCall.J + 1) = (q.cellCall.J + 1) + (q.cellCall.J + 1)
    by ring, pow_add]
  exact Nat.mul_le_mul (hcoord 0) (hcoord 1)

/-- `#{ρ_Y} ≤ p^2` for `p ≥ 1`. -/
theorem card_residueSet_le (p : ℕ) (hp : 1 ≤ p) : (residueSet q p).card ≤ p ^ 2 := by
  classical
  have hcoord : ∀ j : Fin 2, ((if j ∈ Builder.circuitSet q.call then Finset.Ico (0 : ℤ) p else {0}) :
      Finset ℤ).card ≤ p := by
    intro j
    split
    · rw [Int.card_Ico]
      simp
    · simpa using hp
  unfold residueSet
  rw [Fintype.card_piFinset, Fin.prod_univ_two, pow_two]
  exact Nat.mul_le_mul (hcoord 0) (hcoord 1)

theorem one_le_of_mem_primes {p : ℕ} (hp : p ∈ q.cellCall.primes) : 1 ≤ p := by
  have h : p ∈ q.selected.1.primes := hp
  rw [(rules q).primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at h
  exact h.2.1.one_lt.le

/-- The indices `(s, σ, δ, p, ρ_Y)` of the tables printed by a child (Step 3 of `sec:algorithm`). -/
noncomputable def tableIndices : Finset (Bool × Cycle.SignPattern Algorithm.traceOrder ×
    (Fin 2 → Fin (q.cellCall.J + 1) → ℤ) × Σ _ : ℕ, Fin 2 → ℤ) :=
  Finset.univ ×ˢ Finset.univ ×ˢ digitSet q ×ˢ q.cellCall.primes.sigma fun p => residueSet q p

/-- **At most `tableCount` tables** (`prop:time`). -/
theorem card_tableIndices_le : (tableIndices q).card ≤ tableCount q := by
  have hD := card_digitSet_le q
  have hR : (q.cellCall.primes.sigma fun p => residueSet q p).card ≤ q.selected.1.P ^ 3 := by
    rw [Finset.card_sigma]
    calc ∑ p ∈ q.cellCall.primes, (residueSet q p).card ≤ ∑ _p ∈ q.cellCall.primes, q.selected.1.P ^ 2 :=
          Finset.sum_le_sum fun p hp => (card_residueSet_le q p (one_le_of_mem_primes q hp)).trans
            (Nat.pow_le_pow_left (le_P_of_mem_primes q hp) 2)
      _ = q.cellCall.primes.card * q.selected.1.P ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ q.selected.1.P * q.selected.1.P ^ 2 := Nat.mul_le_mul_right _ (card_primes_le q)
      _ = q.selected.1.P ^ 3 := by ring
  unfold tableIndices tableCount
  rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
    Fintype.card_bool, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  calc 2 * (2 ^ (2 * Algorithm.traceOrder) * ((digitSet q).card *
        (q.cellCall.primes.sigma fun p => residueSet q p).card))
      ≤ 2 * (2 ^ (2 * Algorithm.traceOrder) * (q.selected.1.P ^ (2 * (q.cellCall.J + 1)) *
        q.selected.1.P ^ 3)) := by gcongr
    _ = 2 * 4 ^ Algorithm.traceOrder * q.selected.1.P ^ (2 * (q.cellCall.J + 1) + 3) := by
        rw [pow_mul, pow_add]
        norm_num
        ring

/-- The indices `(s, σ, δ, z)` of the systems solved by a child (Step 3 of `sec:algorithm`). -/
noncomputable def systemIndices : Finset (Bool × Cycle.SignPattern Algorithm.traceOrder ×
    (Fin 2 → Fin (q.cellCall.J + 1) → ℤ) × Fin q.cellCall.ncol) :=
  Finset.univ ×ˢ Finset.univ ×ˢ digitSet q ×ˢ Finset.univ

/-- **At most `systemCount` systems** (`prop:time`). -/
theorem card_systemIndices_le : (systemIndices q).card ≤ systemCount q := by
  have hD := card_digitSet_le q
  unfold systemIndices systemCount
  rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
    Finset.card_univ, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]
  calc 2 * (2 ^ (2 * Algorithm.traceOrder) * ((digitSet q).card * q.cellCall.ncol))
      ≤ 2 * (2 ^ (2 * Algorithm.traceOrder) * (q.selected.1.P ^ (2 * (q.cellCall.J + 1)) * q.cellCall.ncol)) := by
        gcongr
    _ = 2 * q.cellCall.ncol * 4 ^ Algorithm.traceOrder * q.selected.1.P ^ (2 * (q.cellCall.J + 1)) := by
        rw [pow_mul]
        norm_num
        ring

/-- **At most `rowCount = P^3` rows per system** (`prop:time`). -/
theorem systemRows_length_le (π : List Bool) (s : Bool) (z : Fin q.cellCall.ncol)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) :
    (systemOf q.cellCall π s z σ δ).rows.length ≤ rowCount q := by
  classical
  have hlen : ∀ p, (residueList q.cellCall z p).length = (residueSet q p).card := by
    intro p
    rw [← List.toFinset_card_of_nodup]
    · congr 1
      ext ρ
      rw [List.mem_toFinset, mem_residueList, residueVectors_eq]
    · unfold residueList residueAxis
      refine List.Nodup.map (fun a b h => ?_) (List.Nodup.product ?_ ?_)
      · have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
        exact Prod.ext h0 h1
      · split
        · exact List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
        · exact List.nodup_singleton 0
      · split
        · exact List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
        · exact List.nodup_singleton 0
  show (systemRows q.cellCall _ z σ δ).length ≤ rowCount q
  unfold systemRows rowCount
  rw [List.length_flatMap]
  calc (List.map (fun p => (List.map (fun ρ => systemRow q.cellCall (splitWeight q.cellCall π s) z σ δ p ρ)
        (residueList q.cellCall z p)).length) (primeList q.cellCall)).sum
      = ((primeList q.cellCall).map fun p => (residueSet q p).card).sum := by
        congr 1
        refine List.map_congr_left fun p _ => ?_
        rw [List.length_map, hlen]
    _ ≤ ((primeList q.cellCall).map fun _ => q.selected.1.P ^ 2).sum := by
        refine List.sum_le_sum fun p hp => ?_
        have hp' := (mem_primeList _ p).mp hp
        exact (card_residueSet_le q p (one_le_of_mem_primes q hp')).trans
          (Nat.pow_le_pow_left (le_P_of_mem_primes q hp') 2)
    _ = q.cellCall.primes.card * q.selected.1.P ^ 2 := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul]
        unfold primeList
        rw [Finset.length_sort]
    _ ≤ q.selected.1.P * q.selected.1.P ^ 2 := Nat.mul_le_mul_right _ (card_primes_le q)
    _ = q.selected.1.P ^ 3 := by ring

end Counts

end NearQuarticWires.Reconstruct
