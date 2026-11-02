import Proof.Quartic.Greedy.Child

/-!
# The exact systems of Step 3 for the two parts of the weights

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and step (1) of the proof of `prop:sound`.

The weights `2^S c_π(w)` are split into their positive and negative parts `g^±` (`splitWeight`). For each part, on
a certified column `z`, a pattern `σ` with `κ_σ ≠ 0` and a digit vector `δ`:

* the class function `y ↦ Σ_{w : mask_w(z) = 1, E(w) = δ, Y(w) = y} g^±(w)` (`classValueOf`) is supported in the box
  `Bx(δ)` (`classValueOf_support`);
* its push-forward modulo every `p ∈ 𝒫` at `ρ_Y` is the recovered count `𝒩^±(z)`, the centred residue of the printed
  count of `g^±` (`classValueOf_pushforward`, `recoveredCountOf_eq`), because `2 Σ_w |g^±(w)| ≤ 2 Σ_w |2^S c_π(w)|`
  is below `p^e` (the bound of `lem:residue`);
* by `imp:window`, it is the only function supported in `Bx(δ)` with these push-forwards (`splitSolution_unique`).

The recovered counts of a part are nonnegative (`recoveredCountOf_nonneg`), so the systems have natural right sides.
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open Finset

section Systems

variable (C : Algorithm.CellCall)

/-- The class function of an arbitrary weight is supported in the box `Bx(δ)` (`lem:certify`(d), paper/paper.tex). -/
theorem classValueOf_support (H : C.ReconstructionHypotheses) (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ)
    (z : Fin C.ncol) (hz : C.Certified z) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (y : Fin 2 → ℤ)
    (hy : y ∉ C.box z δ) : classValueOf C g z σ δ y = 0 := by
  classical
  unfold classValueOf
  apply Finset.sum_eq_zero
  intro w _
  rw [if_neg]
  rintro ⟨hw, hd, hy'⟩
  exact hy (hy' ▸ C.walkSums_mem_box H z hz σ hσ w hw δ hd)

/-- The push-forward of the class function of an arbitrary weight modulo `p` at `ρ_Y` is the weighted count of the
walks with `mask_w(z) = 1`, digit vector `δ` and walk sums congruent to `ρ_Y`. -/
theorem classValueOf_pushforward (H : C.ReconstructionHypotheses)
    (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ) (z : Fin C.ncol) (hz : C.Certified z)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (p : ℕ) (ρY : Fin 2 → ℤ) :
    (∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]), classValueOf C g z σ δ y) =
      ∑ w, if C.walkMask z w = 1 ∧ C.HasDigits z σ w δ ∧
          (∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) then g w else 0 := by
  classical
  unfold classValueOf
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

/-- `lem:residue` with `lem:certify`(a) and (c), paper/paper.tex, for an arbitrary weight `g` with
`2 Σ_w |g(w)| < p^e`: on a certified column, the recovered count at `(δ mod p, ρ_Y)` is the weighted count of the
walks with `mask_w(z) = 1`, digit vector `δ` and walk sums congruent to `ρ_Y`. -/
theorem recoveredCountOf_eq (H : C.ReconstructionHypotheses) (g : Cycle.Walk C.seed.N Algorithm.traceOrder → ℤ)
    (z : Fin C.ncol) (hz : C.Certified z) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z)
    (p : ℕ) (hp : p ∈ C.primes) (hguard : 2 * ∑ w, |g w| < (p : ℤ) ^ C.e) (ρY : Fin 2 → ℤ)
    (hρ : ρY ∈ C.residueVectors z p) :
    recoveredCountOf C g z σ p δ ρY =
      ∑ w, if C.walkMask z w = 1 ∧ C.HasDigits z σ w δ ∧
          (∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) then g w else 0 := by
  classical
  have hrec := Walks.signed_residue_recovery g
    (Walks.walkMaskPoly Algorithm.traceOrder_pos (C.column z).structural (C.column z).tau (C.column z).Xmax
      (C.column z).X)
    (C.walkMask z)
    (fun w => Walks.certified_walk_mask_exact Algorithm.traceOrder_pos C.k (C.column z) hz w)
    (fun w => Walks.walkMaskInt_abs_le_one Algorithm.traceOrder_pos _ _ _ w)
    p (H.prime p hp) C.e H.e_pos (C.residueForms z σ) (C.residueTarget z p δ ρY) hguard
  unfold recoveredCountOf printedCountOf
  rw [hrec]
  unfold Walks.residueCount
  apply Finset.sum_congr rfl
  intro w _
  have hδj : ∀ j ∈ (C.column z).circuits, ∀ r, (δ j r).natAbs < (C.column z).hE := by
    intro j hj r
    unfold Algorithm.CellCall.digitVectors at hδ
    rw [Fintype.mem_piFinset] at hδ
    have h := hδ j
    rw [if_pos hj, Fintype.mem_piFinset] at h
    have h' := Finset.mem_Ioo.mp (h r)
    omega
  have hρj : ∀ j, j ∉ (C.column z).circuits → ρY j = 0 := by
    intro j hj
    unfold Algorithm.CellCall.residueVectors at hρ
    rw [Fintype.mem_piFinset] at hρ
    have h := hρ j
    rw [if_neg hj] at h
    simpa using h
  rcases C.walkMask_mem z w with h0 | h1
  · rw [h0]
    have hne : ¬ ((0 : ℤ) = 1 ∧ C.HasDigits z σ w δ ∧
        ∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) := fun h => absurd h.1 (by norm_num)
    rw [if_neg hne]
    split_ifs <;> simp
  · rw [h1, mul_one]
    have hiff : (∀ f, C.residueForms z σ w f ≡ C.residueTarget z p δ ρY f [ZMOD (p : ℤ)]) ↔
        (C.HasDigits z σ w δ ∧ ∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]) := by
      constructor
      · intro hall
        constructor
        · intro j hj
          have hmod : ∀ r, (C.column z).E j σ w r ≡ δ j r [ZMOD (p : ℤ)] := by
            intro r
            have h := hall (j, some r)
            simp only [Algorithm.CellCall.residueForms, Algorithm.CellCall.residueTarget, if_pos hj] at h
            exact h.trans (Int.mod_modEq _ _)
          exact (Walks.certified_digits_mod_iff Algorithm.traceOrder_pos C.k (C.column z) hz j hj σ hσ w h1 (δ j)
            (hδj j hj) p (H.width z p hp)).mp hmod
        · intro j
          by_cases hj : j ∈ (C.column z).circuits
          · have h := hall (j, none)
            simp only [Algorithm.CellCall.residueForms, Algorithm.CellCall.residueTarget, if_pos hj] at h
            simpa only [Algorithm.CellCall.walkSums, if_pos hj] using h
          · simp only [Algorithm.CellCall.walkSums, if_neg hj, hρj j hj]
            rfl
      · rintro ⟨hd, hy⟩ ⟨j, f⟩
        by_cases hj : j ∈ (C.column z).circuits
        · cases f with
          | some r =>
            simp only [Algorithm.CellCall.residueForms, Algorithm.CellCall.residueTarget, if_pos hj]
            rw [hd j hj r]
            exact (Int.mod_modEq _ _).symm
          | none =>
            simp only [Algorithm.CellCall.residueForms, Algorithm.CellCall.residueTarget, if_pos hj]
            simpa only [Algorithm.CellCall.walkSums, if_pos hj] using hy j
        · simp only [Algorithm.CellCall.residueForms, Algorithm.CellCall.residueTarget, if_neg hj]
          rfl
    by_cases hc : C.HasDigits z σ w δ ∧ ∀ j, C.walkSums z σ w j ≡ ρY j [ZMOD (p : ℤ)]
    · rw [if_pos (hiff.mpr hc), if_pos ⟨rfl, hc.1, hc.2⟩]
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg (fun h => hc ⟨h.2.1, h.2.2⟩)]

/-- The bound of `lem:residue` for a part of the weights: `2 Σ_w |g^±(w)| ≤ 2 Σ_w |2^S c_π(w)| < p^e`. -/
theorem splitWeight_guard (H : C.ReconstructionHypotheses) (π : List Bool) (hπ : π.length ≤ C.seedLength)
    (s : Bool) (p : ℕ) (hp : p ∈ C.primes) :
    2 * ∑ w, |splitWeight C π s w| < (p : ℤ) ^ C.e := by
  refine lt_of_le_of_lt ?_ (H.guard p hp π hπ)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro w _
  rw [abs_of_nonneg (splitWeight_nonneg C π s w)]
  exact splitWeight_le_abs C π s w

/-- The recovered counts of a part of the weights are nonnegative: the right sides of its systems are natural. -/
theorem recoveredCountOf_nonneg (H : C.ReconstructionHypotheses) (π : List Bool) (hπ : π.length ≤ C.seedLength)
    (s : Bool) (z : Fin C.ncol) (hz : C.Certified z) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z)
    (p : ℕ) (hp : p ∈ C.primes) (ρY : Fin 2 → ℤ) (hρ : ρY ∈ C.residueVectors z p) :
    0 ≤ recoveredCountOf C (splitWeight C π s) z σ p δ ρY := by
  classical
  rw [recoveredCountOf_eq C H _ z hz σ hσ δ hδ p hp (splitWeight_guard C H π hπ s p hp) ρY hρ]
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact splitWeight_nonneg C π s w
  · exact le_refl _

/-- **The class function of a part of the weights solves its system** (`prop:sound`, paper/paper.tex): it is
supported in `Bx(δ)`, and its push-forwards are the recovered counts. -/
theorem classValueOf_solves (H : C.ReconstructionHypotheses) (π : List Bool) (hπ : π.length ≤ C.seedLength)
    (s : Bool) (z : Fin C.ncol) (hz : C.Certified z) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z) :
    (∀ y, y ∉ C.box z δ → classValueOf C (splitWeight C π s) z σ δ y = 0) ∧
      ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
        (∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]),
          classValueOf C (splitWeight C π s) z σ δ y) = recoveredCountOf C (splitWeight C π s) z σ p δ ρY := by
  refine ⟨fun y hy => classValueOf_support C H _ z hz σ hσ δ y hy, fun p hp ρY hρ => ?_⟩
  rw [classValueOf_pushforward C H _ z hz σ hσ δ p ρY,
    recoveredCountOf_eq C H _ z hz σ hσ δ hδ p hp (splitWeight_guard C H π hπ s p hp) ρY hρ]

/-- **Uniqueness** (`imp:window`, paper/paper.tex, as in `prop:sound`): every rational function
supported in `Bx(δ)` whose push-forwards modulo every `p ∈ 𝒫` are the recovered counts of a part of the weights is
the class function of that part. -/
theorem splitSolution_unique (H : C.ReconstructionHypotheses) (π : List Bool) (hπ : π.length ≤ C.seedLength)
    (s : Bool) (z : Fin C.ncol) (hz : z ∈ C.certifiedColumns) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z)
    (F : (Fin 2 → ℤ) → ℚ) (hsupp : ∀ y, y ∉ C.box z δ → F y = 0)
    (hpush : ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
      (∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]), F y) =
        (recoveredCountOf C (splitWeight C π s) z σ p δ ρY : ℚ)) (y : Fin 2 → ℤ) :
    F y = (classValueOf C (splitWeight C π s) z σ δ y : ℚ) := by
  have hcert : C.Certified z := by
    classical
    unfold Algorithm.CellCall.certifiedColumns at hz
    exact (Finset.mem_filter.mp hz).2
  obtain ⟨hs1, hs2⟩ := classValueOf_solves C H π hπ s z hcert σ hσ δ hδ
  have h := H.window z hz δ hδ (fun y => F y - (classValueOf C (splitWeight C π s) z σ δ y : ℚ))
    (fun y hy => by rw [hsupp y hy, hs1 y hy, Int.cast_zero, sub_self])
    (fun p hp ρY hρ => by
      rw [Finset.sum_sub_distrib, hpush p hp ρY hρ, ← hs2 p hp ρY hρ, Int.cast_sum, sub_self]) y
  exact sub_eq_zero.mp h

end Systems

end NearQuarticWires.Greedy
