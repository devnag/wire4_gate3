import Proof.Quartic.Algorithm.Algorithm

/-!
# Step (1) of `prop:sound`: the printed sums are exact

Paper: proof of `prop:sound`, step (1), paper/paper.tex.

Fix a certified column `z`, a prefix `π` and a pattern `σ` with `κ_σ ≠ 0`. For a digit vector `δ`, the function
`H_{z,σ,δ}(y) = Σ_{w : mask_w(z) = 1, E(w) = δ} 2^S c_π(w) 1[Y_{·,σ}(z,w) = y]` (`classFunction`)
* is supported in the box `Bx(δ)` (`lem:certify`(d));
* has push-forwards modulo every `p ∈ 𝒫` equal to the recovered counts `𝒩(z)` (`lem:residue` with
  `lem:certify`(a) and (c));
* is therefore the unique solution of the system (`imp:window`), so `v_{z,σ,δ} = H_{z,σ,δ}(0)`.
Every walk with `mask_w(z) = 1` has its digit vector in the enumerated range (`lem:certify`(b)), so summing over `δ`
gives `Σ_w 2^S c_π(w) mask_w(z) 1[Y_{1,σ} = 0] 1[Y_{2,σ} = 0]`; with `cor:conditional` this is
`Ψ̃(π) = 2^S (4^m / 2|Θ|) Ψ(π)`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Algorithm

open Finset
open NearQuarticWires.Sampler (Cell Frequency omega)

namespace CellCall

variable (C : CellCall)

/-- The hypotheses under which step (1) of `prop:sound` holds (paper/paper.tex).
* `prime`, `e_pos`, `guard`: the primes of `𝒫`, the exponent `e ≥ 1` and the bound
  `p^e > 2 · 2^S Σ_w |c_π(w)|` derived in `sec:params`, the hypothesis of `lem:residue`;
* `width`: `2h_E - 1 ≤ p`, from `h_E = ⌊P/4⌋` and `p > P/2` (`lem:certify`(c));
* `A_pos`: the chain product `A` is positive (`imp:chain`(i));
* `residual_le`: `|R_j| ≤ G_j` (`lem:identity`);
* `residual_zero`: `R_j = 0` for a circuit outside `𝒥` (`sec:cycle`: `Y_{2,σ} ≡ 0` if `2 ∉ 𝒥`);
* `window`: `imp:window`(a) (one score, `L_w = D'`) and (b) (two scores, `L_w = L_2`), applied to
  the boxes `Bx(δ)` whose sides have at most `L_w` points (`lem:certify`(d)): a rational function supported on
  `Bx(δ)` whose push-forwards modulo every `p ∈ 𝒫` vanish is zero. -/
structure ReconstructionHypotheses : Prop where
  prime : ∀ p ∈ C.primes, p.Prime
  e_pos : 1 ≤ C.e
  guard : ∀ p ∈ C.primes, ∀ π : List Bool, π.length ≤ C.seedLength →
    2 * ∑ w, |C.walkWeight π w| < (p : ℤ) ^ C.e
  width : ∀ z, ∀ p ∈ C.primes, 2 * ((C.column z).hE : ℤ) - 1 ≤ p
  A_pos : ∀ z, 0 < (C.column z).A
  residual_le : ∀ z j c, |(C.column z).residual j c| ≤ C.G j
  residual_zero : ∀ z j, j ∉ (C.column z).circuits → ∀ c, (C.column z).residual j c = 0
  window : ∀ z ∈ C.certifiedColumns, ∀ δ ∈ C.digitVectors z, ∀ D : (Fin 2 → ℤ) → ℚ,
    (∀ y, y ∉ C.box z δ → D y = 0) →
    (∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
      (∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]), D y) = 0) →
    ∀ y, D y = 0

/-- `lem:cycle`, paper/paper.tex: the integer walk mask `mask_w(z) = Π_l mask(z, e_l)`. -/
def walkMask (z : Fin C.ncol) (w : Cycle.Walk C.seed.N traceOrder) : ℤ :=
  Walks.walkMaskInt traceOrder_pos (C.column z).structural (C.column z).tau (C.column z).X w

/-- `sec:walks`, paper/paper.tex: the vector of walk sums `Y_{j,σ}(z, w)`, `j ∈ 𝒥`; circuits
outside `𝒥` carry `0`. -/
def walkSums (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder) (w : Cycle.Walk C.seed.N traceOrder) :
    Fin 2 → ℤ := fun j =>
  if j ∈ (C.column z).circuits then (C.column z).Y traceOrder_pos j σ w else 0

/-- `lem:certify`(c), paper/paper.tex: the walk's digit vector `E_{·,σ}(z, w)` equals `δ`. -/
def HasDigits (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder) (w : Cycle.Walk C.seed.N traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : Prop :=
  ∀ j ∈ (C.column z).circuits, ∀ r, (C.column z).E j σ w r = δ j r

/-- Proof of `prop:sound`, paper/paper.tex: the function
`H_{z,σ,δ}(y) = Σ_{w : mask_w(z) = 1, E(w) = δ} 2^S c_π(w) 1[Y_{·,σ}(z,w) = y]`. -/
noncomputable def classFunction (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (y : Fin 2 → ℤ) : ℚ := by
  classical
  exact ∑ w, if C.walkMask z w = 1 ∧ C.HasDigits z σ w δ ∧ C.walkSums z σ w = y then
    (C.walkWeight π w : ℚ) else 0

instance (z : Fin C.ncol) (σ : Cycle.SignPattern traceOrder) (w : Cycle.Walk C.seed.N traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : Decidable (C.HasDigits z σ w δ) := by
  unfold HasDigits
  infer_instance

theorem walkMask_mem (z : Fin C.ncol) (w : Cycle.Walk C.seed.N traceOrder) :
    C.walkMask z w = 0 ∨ C.walkMask z w = 1 :=
  Walks.walkMaskInt_zero_or_one traceOrder_pos _ _ _ w

/-- `lem:certify`(d), paper/paper.tex: on a certified column, a walk with `mask_w(z) = 1` and
digit vector `δ` has its walk sums in `Bx(δ)`. -/
theorem walkSums_mem_box (H : C.ReconstructionHypotheses) (z : Fin C.ncol) (hz : C.Certified z)
    (σ : Cycle.SignPattern traceOrder) (hσ : Cycle.kappa traceOrder σ ≠ 0)
    (w : Cycle.Walk C.seed.N traceOrder) (hw : C.walkMask z w = 1)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hd : C.HasDigits z σ w δ) :
    C.walkSums z σ w ∈ C.box z δ := by
  classical
  unfold box
  rw [Fintype.mem_piFinset]
  intro j
  by_cases hj : j ∈ (C.column z).circuits
  · simp only [walkSums, hj, if_true]
    exact Walks.certified_walk_sum_in_box traceOrder_pos C.k (C.column z) hz (H.A_pos z) j hj σ hσ
      (C.G j) (H.residual_le z j) w hw (δ j) (hd j hj)
  · simp [walkSums, hj]

/-- Proof of `prop:sound`, paper/paper.tex: `H_{z,σ,δ}` is supported in `Bx(δ)`. -/
theorem classFunction_support (H : C.ReconstructionHypotheses) (π : List Bool) (z : Fin C.ncol)
    (hz : C.Certified z) (σ : Cycle.SignPattern traceOrder) (hσ : Cycle.kappa traceOrder σ ≠ 0)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (y : Fin 2 → ℤ) (hy : y ∉ C.box z δ) :
    C.classFunction π z σ δ y = 0 := by
  classical
  unfold classFunction
  apply Finset.sum_eq_zero
  intro w _
  rw [if_neg]
  rintro ⟨hw, hd, hy'⟩
  exact hy (hy' ▸ C.walkSums_mem_box H z hz σ hσ w hw δ hd)

/-- The push-forward of `H_{z,σ,δ}` modulo `p` at `ρ_Y` is the signed count of the walks with `mask_w(z) = 1`,
digit vector `δ` and walk sums congruent to `ρ_Y`. -/
theorem classFunction_pushforward (H : C.ReconstructionHypotheses) (π : List Bool) (z : Fin C.ncol)
    (hz : C.Certified z) (σ : Cycle.SignPattern traceOrder) (hσ : Cycle.kappa traceOrder σ ≠ 0)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (p : ℕ) (ρY : Fin 2 → ℤ) :
    (∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]), C.classFunction π z σ δ y) =
      ∑ w, if C.walkMask z w = 1 ∧ C.HasDigits z σ w δ ∧
          (∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) then (C.walkWeight π w : ℚ) else 0 := by
  classical
  unfold classFunction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hc : C.walkMask z w = 1 ∧ C.HasDigits z σ w δ
  · have hbox := C.walkSums_mem_box H z hz σ hσ w hc.1 δ hc.2
    by_cases hm : ∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]
    · rw [if_pos ⟨hc.1, hc.2, hm⟩]
      rw [Finset.sum_eq_single (C.walkSums z σ w)]
      · rw [if_pos ⟨hc.1, hc.2, rfl⟩]
      · intro y _ hy
        rw [if_neg]
        rintro ⟨_, _, h⟩
        exact hy h.symm
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨hbox, hm⟩) h
    · rw [if_neg (fun h => hm h.2.2)]
      apply Finset.sum_eq_zero
      intro y hy
      rw [if_neg]
      rintro ⟨_, _, h⟩
      subst h
      exact hm (Finset.mem_filter.mp hy).2
  · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩)]

/-- `lem:residue` with `lem:certify`(a) and (c), paper/paper.tex: on a certified
column, the recovered count `𝒩(z)` at `(δ mod p, ρ_Y)` is the signed count of the walks with `mask_w(z) = 1`,
digit vector `δ` and walk sums congruent to `ρ_Y`. -/
theorem recoveredCount_eq (H : C.ReconstructionHypotheses) (π : List Bool) (hπ : π.length ≤ C.seedLength)
    (z : Fin C.ncol) (hz : C.Certified z) (σ : Cycle.SignPattern traceOrder)
    (hσ : Cycle.kappa traceOrder σ ≠ 0) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z)
    (p : ℕ) (hp : p ∈ C.primes) (ρY : Fin 2 → ℤ) (hρ : ρY ∈ C.residueVectors z p) :
    (C.recoveredCount π z σ p δ ρY : ℚ) =
      ∑ w, if C.walkMask z w = 1 ∧ C.HasDigits z σ w δ ∧
          (∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) then (C.walkWeight π w : ℚ) else 0 := by
  classical
  have hrec := Walks.signed_residue_recovery (C.walkWeight π)
    (Walks.walkMaskPoly traceOrder_pos (C.column z).structural (C.column z).tau (C.column z).Xmax
      (C.column z).X)
    (C.walkMask z)
    (fun w => Walks.certified_walk_mask_exact traceOrder_pos C.k (C.column z) hz w)
    (fun w => Walks.walkMaskInt_abs_le_one traceOrder_pos _ _ _ w)
    p (H.prime p hp) C.e H.e_pos (C.residueForms z σ) (C.residueTarget z p δ ρY) (H.guard p hp π hπ)
  unfold recoveredCount printedCount
  rw [hrec]
  unfold Walks.residueCount
  push_cast
  apply Finset.sum_congr rfl
  intro w _
  -- the digit vector `δ` lies in the certified window
  have hδj : ∀ j ∈ (C.column z).circuits, ∀ r, (δ j r).natAbs < (C.column z).hE := by
    intro j hj r
    unfold digitVectors at hδ
    rw [Fintype.mem_piFinset] at hδ
    have h := hδ j
    rw [if_pos hj, Fintype.mem_piFinset] at h
    have h' := Finset.mem_Ioo.mp (h r)
    omega
  have hρj : ∀ j, j ∉ (C.column z).circuits → ρY j = 0 := by
    intro j hj
    unfold residueVectors at hρ
    rw [Fintype.mem_piFinset] at hρ
    have h := hρ j
    rw [if_neg hj] at h
    simpa using h
  rcases C.walkMask_mem z w with h0 | h1
  · rw [h0]
    have hne : ¬ ((0 : ℤ) = 1 ∧ C.HasDigits z σ w δ ∧
        ∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) := fun h => absurd h.1 (by norm_num)
    rw [if_neg hne]
    split_ifs
    · rw [Int.cast_zero, mul_zero]
    · rfl
  · have h1' : Walks.walkMaskInt traceOrder_pos (C.column z).structural (C.column z).tau
        (C.column z).X w = 1 := h1
    rw [h1, Int.cast_one, mul_one]
    -- the congruence conditions on the printed forms
    have hiff : (∀ f, C.residueForms z σ w f ≡ C.residueTarget z p δ ρY f [ZMOD (p : ℤ)]) ↔
        (C.HasDigits z σ w δ ∧ ∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) := by
      constructor
      · intro hall
        constructor
        · intro j hj
          have hmod : ∀ r, (C.column z).E j σ w r ≡ δ j r [ZMOD (p : ℤ)] := by
            intro r
            have h := hall (j, some r)
            simp only [residueForms, residueTarget, if_pos hj] at h
            exact h.trans (Int.mod_modEq _ _)
          exact (Walks.certified_digits_mod_iff traceOrder_pos C.k (C.column z) hz j hj σ hσ w h1 (δ j)
            (hδj j hj) p (H.width z p hp)).mp hmod
        · intro j
          by_cases hj : j ∈ (C.column z).circuits
          · have h := hall (j, none)
            simp only [residueForms, residueTarget, if_pos hj] at h
            simpa only [walkSums, if_pos hj] using h
          · simp only [walkSums, if_neg hj, hρj j hj]
            rfl
      · rintro ⟨hd, hy⟩ ⟨j, f⟩
        by_cases hj : j ∈ (C.column z).circuits
        · cases f with
          | some r =>
            simp only [residueForms, residueTarget, if_pos hj]
            rw [hd j hj r]
            exact (Int.mod_modEq _ _).symm
          | none =>
            simp only [residueForms, residueTarget, if_pos hj]
            simpa only [walkSums, if_pos hj] using hy j
        · simp only [residueForms, residueTarget, if_neg hj]
          rfl
    by_cases hc : C.HasDigits z σ w δ ∧ ∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]
    · rw [if_pos (hiff.mpr hc), if_pos ⟨rfl, hc.1, hc.2⟩]
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg (fun h => hc ⟨h.2.1, h.2.2⟩)]

/-- Proof of `prop:sound`, paper/paper.tex: by `imp:window`, the system of a certified column has
the unique solution `H_{z,σ,δ}`, so `v_{z,σ,δ} = H_{z,σ,δ}(0)`. -/
theorem reconstructedValue_eq (H : C.ReconstructionHypotheses) (π : List Bool)
    (hπ : π.length ≤ C.seedLength) (z : Fin C.ncol) (hz : z ∈ C.certifiedColumns)
    (σ : Cycle.SignPattern traceOrder) (hσ : Cycle.kappa traceOrder σ ≠ 0)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z) :
    (∃ H', C.Solves π z σ δ H') ∧ C.reconstructedValue π z σ δ = C.classFunction π z σ δ 0 := by
  classical
  have hcert : C.Certified z := by
    unfold certifiedColumns at hz
    exact (Finset.mem_filter.mp hz).2
  have hsolves : C.Solves π z σ δ (C.classFunction π z σ δ) := by
    refine ⟨fun y hy => C.classFunction_support H π z hcert σ hσ δ y hy, ?_⟩
    intro p hp ρY hρ
    rw [C.classFunction_pushforward H π z hcert σ hσ δ p ρY,
      C.recoveredCount_eq H π hπ z hcert σ hσ δ hδ p hp ρY hρ]
  have hunique : ∀ H', C.Solves π z σ δ H' → H' = C.classFunction π z σ δ := by
    intro H' hH'
    funext y
    have h := H.window z hz δ hδ (fun y => H' y - C.classFunction π z σ δ y)
      (fun y hy => by rw [hH'.1 y hy, hsolves.1 y hy, sub_self])
      (fun p hp ρY hρ => by
        rw [Finset.sum_sub_distrib, hH'.2 p hp ρY hρ, hsolves.2 p hp ρY hρ, sub_self]) y
    exact sub_eq_zero.mp h
  refine ⟨⟨_, hsolves⟩, ?_⟩
  unfold reconstructedValue
  rw [dif_pos ⟨_, hsolves⟩]
  rw [hunique _ (Classical.choose_spec (⟨_, hsolves⟩ : ∃ H', C.Solves π z σ δ H'))]

/-- `lem:certify`(b), paper/paper.tex: on a certified column, a walk with
`mask_w(z) = 1` has exactly one digit vector in the enumerated range. -/
theorem digitVectors_filter (z : Fin C.ncol) (hz : C.Certified z) (σ : Cycle.SignPattern traceOrder)
    (hσ : Cycle.kappa traceOrder σ ≠ 0) (w : Cycle.Walk C.seed.N traceOrder) (hw : C.walkMask z w = 1) :
    ∃ δ₀ ∈ C.digitVectors z, ∀ δ ∈ C.digitVectors z, C.HasDigits z σ w δ ↔ δ = δ₀ := by
  classical
  refine ⟨fun j r => if j ∈ (C.column z).circuits then (C.column z).E j σ w r else 0, ?_, ?_⟩
  · unfold digitVectors
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j ∈ (C.column z).circuits
    · rw [if_pos hj, Fintype.mem_piFinset]
      intro r
      have hb := Walks.certified_digit_bound traceOrder_pos C.k (C.column z) hz j hj σ hσ r w hw
      simp only [if_pos hj, Finset.mem_Ioo]
      omega
    · simp only [if_neg hj, Finset.mem_singleton]
      rfl
  · intro δ hδ
    constructor
    · intro hd
      funext j r
      by_cases hj : j ∈ (C.column z).circuits
      · simp only [if_pos hj]
        exact (hd j hj r).symm
      · unfold digitVectors at hδ
        rw [Fintype.mem_piFinset] at hδ
        have h := hδ j
        rw [if_neg hj] at h
        have h' : δ j = 0 := Finset.mem_singleton.mp h
        simp only [if_neg hj, h']
        rfl
    · rintro rfl j hj r
      simp only [if_pos hj]

/-- Proof of `prop:sound`, paper/paper.tex: on a certified column and for `κ_σ ≠ 0`,
`Σ_δ v_{z,σ,δ} = Σ_w 2^S c_π(w) mask_w(z) 1[Y_{1,σ} = 0] 1[Y_{2,σ} = 0]`. -/
theorem sum_reconstructedValue (H : C.ReconstructionHypotheses) (π : List Bool)
    (hπ : π.length ≤ C.seedLength) (z : Fin C.ncol) (hz : z ∈ C.certifiedColumns)
    (σ : Cycle.SignPattern traceOrder) (hσ : Cycle.kappa traceOrder σ ≠ 0) :
    (∑ δ ∈ C.digitVectors z, C.reconstructedValue π z σ δ) =
      ∑ w, (C.walkWeight π w : ℚ) * (C.walkMask z w : ℚ) *
        ((if Cycle.walkSum traceOrder_pos ((C.column z).residual 0) σ w = 0 then 1 else 0) *
          (if Cycle.walkSum traceOrder_pos ((C.column z).residual 1) σ w = 0 then 1 else 0)) := by
  classical
  have hcert : C.Certified z := by
    unfold certifiedColumns at hz
    exact (Finset.mem_filter.mp hz).2
  rw [Finset.sum_congr rfl fun δ hδ => (C.reconstructedValue_eq H π hπ z hz σ hσ δ hδ).2]
  unfold classFunction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rcases C.walkMask_mem z w with h0 | h1
  · rw [h0]
    simp only [Int.cast_zero, mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro δ _
    rw [if_neg]
    rintro ⟨h, _⟩
    exact absurd h (by norm_num)
  · rw [h1]
    obtain ⟨δ₀, hδ₀, huniq⟩ := C.digitVectors_filter z hcert σ hσ w h1
    rw [Finset.sum_eq_single δ₀]
    · have hd₀ : C.HasDigits z σ w δ₀ := (huniq δ₀ hδ₀).mpr rfl
      -- the walk sums vanish iff both residual walk sums vanish
      have hY : C.walkSums z σ w = 0 ↔
          (Cycle.walkSum traceOrder_pos ((C.column z).residual 0) σ w = 0 ∧
            Cycle.walkSum traceOrder_pos ((C.column z).residual 1) σ w = 0) := by
        have hcol : ∀ j, C.walkSums z σ w j = 0 ↔
            Cycle.walkSum traceOrder_pos ((C.column z).residual j) σ w = 0 := by
          intro j
          by_cases hj : j ∈ (C.column z).circuits
          · simp only [walkSums, if_pos hj]
            rfl
          · simp only [walkSums, if_neg hj, true_iff]
            unfold Cycle.walkSum
            simp [H.residual_zero z j hj]
        constructor
        · intro h
          exact ⟨(hcol 0).mp (congrFun h 0), (hcol 1).mp (congrFun h 1)⟩
        · rintro ⟨a, b⟩
          funext j
          fin_cases j
          · exact (hcol 0).mpr a
          · exact (hcol 1).mpr b
      by_cases hz0 : C.walkSums z σ w = 0
      · rw [if_pos ⟨rfl, hd₀, hz0⟩]
        obtain ⟨a, b⟩ := hY.mp hz0
        simp [a, b]
      · rw [if_neg (fun h => hz0 h.2.2)]
        by_cases a : Cycle.walkSum traceOrder_pos ((C.column z).residual 0) σ w = 0
        · by_cases b : Cycle.walkSum traceOrder_pos ((C.column z).residual 1) σ w = 0
          · exact absurd (hY.mpr ⟨a, b⟩) hz0
          · simp [b]
        · simp [a]
    · intro δ hδ hne
      rw [if_neg]
      rintro ⟨_, hd, _⟩
      exact hne ((huniq δ hδ).mp hd)
    · intro h
      exact absurd hδ₀ h

end CellCall

end NearQuarticWires.Algorithm
