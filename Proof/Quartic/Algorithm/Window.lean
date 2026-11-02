import Proof.Quartic.Algorithm.Sound
import Proof.Gates.ScalarWindow
import Proof.Gates.TwoScoreWindow
import Proof.Quartic.Algorithm.Parameters

/-!
# `imp:window` on the boxes of the reconstruction

Paper: `imp:window`, paper/paper.tex, and `lem:certify`(d).

`WindowOne` and `WindowTwo` are parts (a) and (b) of `imp:window`, in the form "a rational function supported on
the window whose push-forwards modulo every `p ∈ 𝒫` vanish is zero" (equivalent, by linearity, to "is uniquely
determined by its push-forwards"). From them, and from the box sizes of `lem:certify`(d), this file derives the
uniqueness statement on the boxes `Bx(δ)` that the reconstruction step uses
(`ReconstructionHypotheses.window`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Algorithm

open Finset

/-- `imp:window`(a), paper/paper.tex: a rational function supported on at most `D'` consecutive
integers with `F_p = 0` for all `p ∈ 𝒫` is zero. -/
def WindowOne (primes : Finset ℕ) (Dprime : ℕ) : Prop :=
  ∀ (F : ℤ → ℚ) (lo hi : ℤ), (Finset.Icc lo hi).card ≤ Dprime → (∀ y, y ∉ Finset.Icc lo hi → F y = 0) →
    (∀ p ∈ primes, ∀ ρ : ℤ,
      (∑ y ∈ (Finset.Icc lo hi).filter (fun y => y ≡ ρ [ZMOD (p : ℤ)]), F y) = 0) →
    ∀ y, F y = 0

/-- `imp:window`(b), paper/paper.tex: a rational function supported on a box in `ℤ²` with both sides
at most `L_2` whose push-forwards `F_p`, `p ∈ 𝒫`, vanish is zero. -/
def WindowTwo (primes : Finset ℕ) (L2 : ℕ) : Prop :=
  ∀ (F : ℤ × ℤ → ℚ) (lo₁ hi₁ lo₂ hi₂ : ℤ), (Finset.Icc lo₁ hi₁).card ≤ L2 → (Finset.Icc lo₂ hi₂).card ≤ L2 →
    (∀ y, y ∉ Finset.Icc lo₁ hi₁ ×ˢ Finset.Icc lo₂ hi₂ → F y = 0) →
    (∀ p ∈ primes, ∀ ρ₁ ρ₂ : ℤ,
      (∑ y ∈ (Finset.Icc lo₁ hi₁ ×ˢ Finset.Icc lo₂ hi₂).filter
        (fun y => y.1 ≡ ρ₁ [ZMOD (p : ℤ)] ∧ y.2 ≡ ρ₂ [ZMOD (p : ℤ)]), F y) = 0) →
    ∀ y, F y = 0

/-- A sum over the integer interval `[lo, hi]` is a sum over its offsets `0, …, #[lo, hi] - 1`. -/
theorem sum_Icc_eq_sum_fin (lo hi : ℤ) (g : ℤ → ℚ) :
    (∑ y ∈ Finset.Icc lo hi, g y) = ∑ i : Fin (Finset.Icc lo hi).card, g (lo + (i : ℕ)) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map, Finset.card_map, Finset.card_range,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => g (lo + (i : ℤ)))]
  rfl

/-- **`imp:window`(a) from its proof in the base library**: `NearCubicGates.ScalarWindow.zero_of_frameResidueData_zero`
is the one-score window on a translated frame of at most `D' = 1 + Σ_{p ∈ 𝒫}(p - 1)` integers. -/
theorem windowOne_of_frame (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, p.Prime) :
    WindowOne primes (NearCubicGates.ScalarWindow.window primes) := by
  classical
  intro F lo hi hcard hsupp hdata y
  by_cases hy : y ∈ Finset.Icc lo hi
  swap
  · exact hsupp y hy
  set L := (Finset.Icc lo hi).card with hL
  have hzero := NearCubicGates.ScalarWindow.zero_of_frameResidueData_zero primes hne hprime
    (fun i : Fin L => F (lo + (i : ℕ))) lo hcard
    (by
      intro p hp r
      have hp0 : (0 : ℤ) < p := by exact_mod_cast (hprime p hp).pos
      unfold NearCubicGates.ScalarWindow.frameResidueData
      by_cases hr : 0 ≤ r ∧ r < p
      · have h := hdata p hp r
        rw [Finset.sum_filter, sum_Icc_eq_sum_fin] at h
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
        have hiff : (lo + ((i : ℕ) : ℤ)) % (p : ℤ) = r ↔ lo + ((i : ℕ) : ℤ) ≡ r [ZMOD (p : ℤ)] := by
          rw [Int.ModEq, Int.emod_eq_of_lt hr.1 hr.2]
        simp only [hiff]
      · apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        intro h
        apply hr
        rw [← h]
        exact ⟨Int.emod_nonneg _ hp0.ne', Int.emod_lt_of_pos _ hp0⟩)
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hy
  have hi : (y - lo).toNat < L := by
    rw [hL, Int.card_Icc]
    omega
  have h := hzero ⟨(y - lo).toNat, hi⟩
  simp only at h
  rwa [show lo + (((y - lo).toNat : ℕ) : ℤ) = y by omega] at h

/-- **`imp:window`(b) from its proof in the base library**: `NearCubicGates.ProjectionBinomials.square_window_zero`
is the two-score window on an `L × L` square with `L ≤ S_φ(⌊(D' - 1)/(L - 1)⌋)`; a box with sides at most `L` is
translated into such a square. -/
theorem windowTwo_of_square (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, p.Prime)
    (L : ℕ) (hL : 2 ≤ L)
    (hsize : L ≤ NearCubicGates.TomographyDirections.degreeSum
      ((NearCubicGates.ScalarWindow.window primes - 1) / (L - 1))) :
    WindowTwo primes L := by
  classical
  intro F lo₁ hi₁ lo₂ hi₂ hc₁ hc₂ hsupp hdata y
  by_cases hy : y ∈ Finset.Icc lo₁ hi₁ ×ˢ Finset.Icc lo₂ hi₂
  swap
  · exact hsupp y hy
  let emb : Fin L × Fin L → ℤ × ℤ := fun i => (lo₁ + (i.1 : ℕ), lo₂ + (i.2 : ℕ))
  have hemb : Function.Injective emb := by
    intro a b h
    simp only [emb, Prod.mk.injEq, add_right_inj, Nat.cast_inj] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  -- every point of the box is a point of the square
  have hcover : ∀ x ∈ Finset.Icc lo₁ hi₁ ×ˢ Finset.Icc lo₂ hi₂, ∃ i, emb i = x := by
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp hx
    obtain ⟨a₁, b₁⟩ := Finset.mem_Icc.mp hx₁
    obtain ⟨a₂, b₂⟩ := Finset.mem_Icc.mp hx₂
    rw [Int.card_Icc] at hc₁ hc₂
    refine ⟨(⟨(x.1 - lo₁).toNat, by omega⟩, ⟨(x.2 - lo₂).toNat, by omega⟩), ?_⟩
    simp only [emb]
    ext <;> simp <;> omega
  have hzero := NearCubicGates.ProjectionBinomials.square_window_zero primes hne hprime L hL
    (fun i => F (emb i)) hsize
    (by
      intro p hp r
      have hp0 : (0 : ℤ) < p := by exact_mod_cast (hprime p hp).pos
      rw [NearCubicGates.TwoScoreProjections.jointData_eq]
      have h := hdata p hp (lo₁ + (r.1 : ℕ)) (lo₂ + (r.2 : ℕ))
      rw [Finset.sum_filter] at h
      refine Eq.trans ?_ h
      -- the residue condition on the square is the congruence condition on the box
      have hcond : ∀ i : Fin L × Fin L,
          ((((i.1 : ℕ) : ℤ) % (p : ℤ) = ((r.1 : ℕ) : ℤ) ∧ (((i.2 : ℕ) : ℤ) % (p : ℤ) = ((r.2 : ℕ) : ℤ))) ↔
            ((emb i).1 ≡ lo₁ + (r.1 : ℕ) [ZMOD (p : ℤ)] ∧ (emb i).2 ≡ lo₂ + (r.2 : ℕ) [ZMOD (p : ℤ)])) := by
        intro i
        have hr₁ : ((r.1 : ℕ) : ℤ) % (p : ℤ) = (r.1 : ℕ) :=
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.1.isLt)
        have hr₂ : ((r.2 : ℕ) : ℤ) % (p : ℤ) = (r.2 : ℕ) :=
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.2.isLt)
        simp only [emb]
        constructor
        · rintro ⟨h₁, h₂⟩
          refine ⟨Int.ModEq.add_left _ ?_, Int.ModEq.add_left _ ?_⟩
          · rw [Int.ModEq, h₁, hr₁]
          · rw [Int.ModEq, h₂, hr₂]
        · rintro ⟨h₁, h₂⟩
          have g₁ := Int.ModEq.add_left_cancel' lo₁ h₁
          have g₂ := Int.ModEq.add_left_cancel' lo₂ h₂
          refine ⟨?_, ?_⟩
          · rw [← hr₁]
            exact g₁
          · rw [← hr₂]
            exact g₂
      simp_rw [hcond]
      rw [← Finset.sum_image (f := fun x : ℤ × ℤ => if x.1 ≡ lo₁ + (r.1 : ℕ) [ZMOD (p : ℤ)] ∧
          x.2 ≡ lo₂ + (r.2 : ℕ) [ZMOD (p : ℤ)] then F x else 0) (fun a _ b _ h => hemb h)]
      symm
      apply Finset.sum_subset
      · intro x hx
        obtain ⟨i, hi⟩ := hcover x hx
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
      · intro x _ hx
        rw [hsupp x hx]
        simp)
  obtain ⟨i, rfl⟩ := hcover y hy
  exact hzero i

/-- `imp:window`(b) when the window has at most one point per side: the box is at most one point, which its own
residue class detects. -/
theorem windowTwo_le_one (primes : Finset ℕ) (hne : primes.Nonempty) (L : ℕ) (hL : L ≤ 1) :
    WindowTwo primes L := by
  classical
  intro F lo₁ hi₁ lo₂ hi₂ hc₁ hc₂ hsupp hdata y
  by_cases hy : y ∈ Finset.Icc lo₁ hi₁ ×ˢ Finset.Icc lo₂ hi₂
  swap
  · exact hsupp y hy
  obtain ⟨p, hp⟩ := hne
  have h := hdata p hp y.1 y.2
  have hone : Finset.Icc lo₁ hi₁ ×ˢ Finset.Icc lo₂ hi₂ = {y} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hy, fun x hx => ?_⟩
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp hx
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_product.mp hy
    exact Prod.ext (Finset.card_le_one.mp (hc₁.trans hL) _ hx₁ _ hy₁)
      (Finset.card_le_one.mp (hc₂.trans hL) _ hx₂ _ hy₂)
  rw [hone, Finset.filter_singleton, if_pos ⟨Int.ModEq.refl _, Int.ModEq.refl _⟩, Finset.sum_singleton] at h
  exact h

/-- **`imp:window`(b) at the computed window** `L_2` of `sec:params` item 6 (`pairWindow`), from the base library. -/
theorem windowTwo_pairWindow (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, p.Prime) :
    WindowTwo primes (pairWindow (NearCubicGates.ScalarWindow.window primes)) := by
  classical
  unfold pairWindow
  simp only
  split_ifs with h0
  · exact windowTwo_le_one primes hne 1 le_rfl
  · have hspec := Nat.findGreatest_of_ne_zero rfl h0
    exact windowTwo_of_square primes hne hprime _ hspec.1 hspec.2

namespace CellCall

variable (C : CellCall)

/-- `lem:certify`(d), paper/paper.tex: the side `Bx_j(δ^{(j)})` of the box. -/
noncomputable def side (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (j : Fin 2) : Finset ℤ :=
  Walks.fullBox ((C.column z).M * Walks.digitValue (C.column z).rate (δ j)) (C.column z).A
    (C.column z).Lambda ((2 * traceOrder : ℕ) * (C.G j : ℤ))

/-- The box of a one-circuit column is the image of its first side. -/
theorem box_eq_one (z : Fin C.ncol) (hz : (C.column z).circuits = {0}) (δ : Fin 2 → Fin (C.J + 1) → ℤ) :
    C.box z δ = (C.side z δ 0).image (fun a => ![a, 0]) := by
  classical
  ext y
  simp only [box, Fintype.mem_piFinset, Finset.mem_image, hz, Finset.mem_singleton]
  constructor
  · intro h
    refine ⟨y 0, ?_, ?_⟩
    · have := h 0
      simpa [side] using this
    · have h1 := h 1
      simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, Finset.mem_singleton] at h1
      funext j
      fin_cases j
      · rfl
      · simpa using h1.symm
  · rintro ⟨a, ha, rfl⟩ j
    fin_cases j
    · simpa [side] using ha
    · simp

/-- The box of a two-circuit column is the image of the product of its sides. -/
theorem box_eq_two (z : Fin C.ncol) (hz : (C.column z).circuits = {0, 1}) (δ : Fin 2 → Fin (C.J + 1) → ℤ) :
    C.box z δ = (C.side z δ 0 ×ˢ C.side z δ 1).image (fun a => ![a.1, a.2]) := by
  classical
  ext y
  simp only [box, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_product, hz, Finset.mem_insert,
    Finset.mem_singleton, Prod.exists]
  constructor
  · intro h
    refine ⟨y 0, y 1, ⟨?_, ?_⟩, ?_⟩
    · simpa [side] using h 0
    · simpa [side] using h 1
    · funext j
      fin_cases j <;> rfl
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩ j
    fin_cases j
    · simpa [side] using ha
    · simpa [side] using hb

theorem sum_filter_image {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β)
    (hg : Function.Injective g) (P : β → Prop) [DecidablePred P] (f : β → ℚ) :
    (∑ y ∈ (s.image g).filter P, f y) = ∑ x ∈ s.filter (fun x => P (g x)), f (g x) := by
  rw [Finset.sum_filter, Finset.sum_image (fun x _ y _ h => hg h), ← Finset.sum_filter]

theorem side_eq_Icc (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (j : Fin 2) :
    ∃ lo hi : ℤ, C.side z δ j = Finset.Icc lo hi :=
  ⟨_, _, rfl⟩

/-- `lem:certify`(d), paper/paper.tex: each side of the box has at most `L` points when
`2Λ - 2 ≤ (L - 1) A`. -/
theorem side_card_le (z : Fin C.ncol) (δ : Fin 2 → Fin (C.J + 1) → ℤ) (j : Fin 2) (L : ℕ)
    (hA : 0 < (C.column z).A) (hw : 2 * ((C.column z).Lambda : ℤ) - 2 ≤ ((L : ℤ) - 1) * (C.column z).A) :
    (C.side z δ j).card ≤ L :=
  Walks.fullBox_card_le _ _ _ _ L hA hw

/-- **`imp:window` on the boxes `Bx(δ)`**, paper/paper.tex with `lem:certify`(d): from parts (a)
and (b) of `imp:window` (with `L_w = D'` for one circuit and `L_w = L_2` for two), a rational function supported on
`Bx(δ)` whose push-forwards modulo every `p ∈ 𝒫` vanish is zero. This is the field
`ReconstructionHypotheses.window`. -/
theorem window_of_paper (Dprime L2 : ℕ) (h1 : WindowOne C.primes Dprime) (h2 : WindowTwo C.primes L2)
    (hp0 : ∀ p ∈ C.primes, 0 < p) (hA : ∀ z, 0 < (C.column z).A)
    (hshape : ∀ z, ((C.column z).circuits = {0} ∧
        2 * ((C.column z).Lambda : ℤ) - 2 ≤ ((Dprime : ℤ) - 1) * (C.column z).A) ∨
      ((C.column z).circuits = {0, 1} ∧
        2 * ((C.column z).Lambda : ℤ) - 2 ≤ ((L2 : ℤ) - 1) * (C.column z).A)) :
    ∀ z ∈ C.certifiedColumns, ∀ δ ∈ C.digitVectors z, ∀ D : (Fin 2 → ℤ) → ℚ,
      (∀ y, y ∉ C.box z δ → D y = 0) →
      (∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
        (∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]), D y) = 0) →
      ∀ y, D y = 0 := by
  classical
  intro z _ δ _ D hsupp hdata y
  by_cases hy : y ∈ C.box z δ
  swap
  · exact hsupp y hy
  rcases hshape z with ⟨hc, hw⟩ | ⟨hc, hw⟩
  · -- one circuit: `imp:window`(a)
    have hinj : Function.Injective (fun a : ℤ => (![a, 0] : Fin 2 → ℤ)) := by
      intro a b h
      simpa using congrFun h 0
    obtain ⟨lo, hi, hside⟩ := C.side_eq_Icc z δ 0
    have hF := h1 (fun a => D ![a, 0]) lo hi
      (by rw [← hside]; exact C.side_card_le z δ 0 Dprime (hA z) hw)
      (by
        intro a ha
        apply hsupp
        rw [C.box_eq_one z hc δ, Finset.mem_image]
        rintro ⟨a', ha', h⟩
        rw [hinj h, hside] at ha'
        exact ha ha')
      (by
        intro p hp ρ
        have hρ : (![ρ % (p : ℤ), 0] : Fin 2 → ℤ) ∈ C.residueVectors z p := by
          have := hp0 p hp
          unfold residueVectors
          rw [Fintype.mem_piFinset, Fin.forall_fin_two]
          refine ⟨?_, ?_⟩
          · rw [if_pos (by simp [hc]), Finset.mem_Ico]
            exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
          · rw [if_neg (by simp [hc])]
            simp
        have h := hdata p hp _ hρ
        rw [C.box_eq_one z hc δ, sum_filter_image _ _ hinj] at h
        rw [← h, ← hside]
        apply Finset.sum_congr
        · ext a
          simp only [Finset.mem_filter, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          constructor
          · rintro ⟨ha, hm⟩
            exact ⟨ha, hm.trans (Int.mod_modEq ρ p).symm, Int.ModEq.refl 0⟩
          · rintro ⟨ha, hm, _⟩
            exact ⟨ha, hm.trans (Int.mod_modEq ρ p)⟩
        · intro a _
          rfl)
    rw [C.box_eq_one z hc δ, Finset.mem_image] at hy
    obtain ⟨a, _, rfl⟩ := hy
    exact hF a
  · -- two circuits: `imp:window`(b)
    have hinj : Function.Injective (fun a : ℤ × ℤ => (![a.1, a.2] : Fin 2 → ℤ)) := by
      intro a b h
      exact Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1)
    obtain ⟨lo₁, hi₁, hside₁⟩ := C.side_eq_Icc z δ 0
    obtain ⟨lo₂, hi₂, hside₂⟩ := C.side_eq_Icc z δ 1
    have hF := h2 (fun a => D ![a.1, a.2]) lo₁ hi₁ lo₂ hi₂
      (by rw [← hside₁]; exact C.side_card_le z δ 0 L2 (hA z) hw)
      (by rw [← hside₂]; exact C.side_card_le z δ 1 L2 (hA z) hw)
      (by
        intro a ha
        apply hsupp
        rw [C.box_eq_two z hc δ, Finset.mem_image]
        rintro ⟨a', ha', h⟩
        rw [hinj h, hside₁, hside₂] at ha'
        exact ha ha')
      (by
        intro p hp ρ₁ ρ₂
        have hρ : (![ρ₁ % (p : ℤ), ρ₂ % (p : ℤ)] : Fin 2 → ℤ) ∈ C.residueVectors z p := by
          have := hp0 p hp
          unfold residueVectors
          rw [Fintype.mem_piFinset, Fin.forall_fin_two]
          refine ⟨?_, ?_⟩
          · rw [if_pos (by simp [hc]), Finset.mem_Ico]
            exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
          · rw [if_pos (by simp [hc]), Finset.mem_Ico]
            exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
        have h := hdata p hp _ hρ
        rw [C.box_eq_two z hc δ, sum_filter_image _ _ hinj] at h
        rw [← h, ← hside₁, ← hside₂]
        apply Finset.sum_congr
        · ext a
          simp only [Finset.mem_filter, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          constructor
          · rintro ⟨ha, hm₁, hm₂⟩
            exact ⟨ha, hm₁.trans (Int.mod_modEq ρ₁ p).symm, hm₂.trans (Int.mod_modEq ρ₂ p).symm⟩
          · rintro ⟨ha, hm₁, hm₂⟩
            exact ⟨ha, hm₁.trans (Int.mod_modEq ρ₁ p), hm₂.trans (Int.mod_modEq ρ₂ p)⟩
        · intro a _
          rfl)
    rw [C.box_eq_two z hc δ, Finset.mem_image] at hy
    obtain ⟨a, _, rfl⟩ := hy
    exact hF a

/-- The modulus bound of `lem:residue` (paper/paper.tex) for a cell call whose seed generator,
primes and exponent are those of the parameters: `p^e > 2 · 2^S Σ_w |c_π(w)|` at every prefix of length at most
`S`. It combines `cor:conditional` (`|2^S c_π(w)| ≤ 2^S (N²Q)^{2m}`, at most `N^{2m}` walks) with
`Parameters.modulus_bound`. -/
theorem guard_of_parameters (Pm : Parameters) (hN : C.seed.N = Pm.N) (hQ : C.seed.Q = Pm.Q)
    (hS : C.seedLength = Pm.S) (hprimes : C.primes = Pm.primes) (he : C.e = Pm.e) :
    ∀ p ∈ C.primes, ∀ π : List Bool, π.length ≤ C.seedLength →
      2 * ∑ w, |C.walkWeight π w| < (p : ℤ) ^ C.e := by
  intro p hp π hπ
  have hb : ∀ w, |C.walkWeight π w| ≤
      (2 : ℤ) ^ C.seedLength * ((C.seed.Q : ℤ) * (C.seed.N : ℤ) ^ 2) ^ 8 :=
    fun w => Cycle.abs_scaledGamma_le C.seed π.length (prefixValue π) hπ w
  have hsum : ∑ w, |C.walkWeight π w| ≤
      (C.seed.N : ℤ) ^ 8 * ((2 : ℤ) ^ C.seedLength * ((C.seed.Q : ℤ) * (C.seed.N : ℤ) ^ 2) ^ 8) := by
    calc ∑ w, |C.walkWeight π w| ≤ ∑ _w : Cycle.Walk C.seed.N traceOrder,
          (2 : ℤ) ^ C.seedLength * ((C.seed.Q : ℤ) * (C.seed.N : ℤ) ^ 2) ^ 8 :=
          Finset.sum_le_sum fun w _ => hb w
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
          simp only [Fintype.card_fin, traceOrder, nsmul_eq_mul]
          push_cast
          ring
  have hmod := Pm.modulus_bound p (hprimes ▸ hp)
  rw [← hN, ← hQ, ← hS] at hmod
  have hmodZ : 2 * (2 : ℤ) ^ C.seedLength * (C.seed.N : ℤ) ^ 8 * ((C.seed.Q : ℤ) * (C.seed.N : ℤ) ^ 2) ^ 8 <
      (p : ℤ) ^ Pm.e := by
    exact_mod_cast hmod
  rw [he]
  nlinarith [hsum, hmodZ]

/-- `lem:certify`(c) premise for a cell call whose columns use the parameters' `h_E` and primes:
`2h_E - 1 ≤ p` for every `p ∈ 𝒫` (from `h_E = ⌊P/4⌋` and `p > P/2`). -/
theorem width_of_parameters (Pm : Parameters) (hprimes : C.primes = Pm.primes)
    (hE : ∀ z, (C.column z).hE = Pm.hE) :
    ∀ z, ∀ p ∈ C.primes, 2 * ((C.column z).hE : ℤ) - 1 ≤ p := by
  intro z p hp
  have h := Pm.width p (hprimes ▸ hp)
  rw [hE z]
  omega

/-- `sec:params` item 4 and `lem:root`: a cell call whose sampler uses the parameters' `N`, `Q`, `η` and whose
dictionary has the parameters' `I = 2|Θ|` matrices satisfies the sampler budget. -/
theorem samplerBudget_of_parameters (Pm : Parameters) (hN : C.seed.N = Pm.N) (hQ : C.seed.Q = Pm.Q)
    (hη : C.η = Pm.eta) (hI : Pm.I = 2 * (Sampler.omega 4 (C.G 0) * Sampler.omega 4 (C.G 1)))
    (hN2 : 2 ≤ C.seed.N) (hNQ : C.seed.N ≤ C.seed.Q) :
    C.SamplerBudget where
  two_le_N := hN2
  N_le_Q := hNQ
  eta_nonneg := by rw [hη]; exact Pm.eta_pos.le
  budget := by
    have h := Pm.budget
    rw [← hN, ← hQ, ← hη, hI] at h
    exact_mod_cast h

/-- `lem:certify`(d) box sizes for a cell call whose columns use the parameters' `Λ`, `A` and circuit set:
`2Λ - 2 ≤ (L_w - 1) A` with `L_w = D'` for one circuit and `L_w = L_2` for two. -/
theorem shape_of_parameters (Pm : Parameters) (hprimes : C.primes = Pm.primes)
    (hcirc : ∀ z, (C.column z).circuits = if Pm.pair then {0, 1} else {0})
    (hΛ : ∀ z, (C.column z).Lambda = Pm.Lambda) (hA : ∀ z, (C.column z).A = (Pm.A : ℤ)) :
    ∀ z, ((C.column z).circuits = {0} ∧
        2 * ((C.column z).Lambda : ℤ) - 2 ≤
          ((NearCubicGates.ScalarWindow.window C.primes : ℤ) - 1) * (C.column z).A) ∨
      ((C.column z).circuits = {0, 1} ∧
        2 * ((C.column z).Lambda : ℤ) - 2 ≤
          ((pairWindow (NearCubicGates.ScalarWindow.window C.primes) : ℤ) - 1) * (C.column z).A) := by
  intro z
  have hb := Pm.box
  have hLw := Pm.Lw_pos
  have hbZ : 2 * (Pm.Lambda : ℤ) - 2 ≤ ((Pm.Lw : ℤ) - 1) * (Pm.A : ℤ) := by
    have h : ((2 * Pm.Lambda : ℕ) : ℤ) ≤ (((Pm.Lw - 1) * Pm.A + 2 : ℕ) : ℤ) := by exact_mod_cast hb
    push_cast [Nat.cast_sub hLw] at h
    linarith
  rw [hΛ z, hA z, hprimes, ← Pm.Dprime_eq, ← Pm.L2_eq]
  have hLweq := Pm.Lw_eq
  cases hpair : Pm.pair
  · left
    rw [hpair] at hLweq
    simp only [Bool.false_eq_true, if_false] at hLweq
    refine ⟨by rw [hcirc z, hpair]; rfl, ?_⟩
    rw [← hLweq]
    exact hbZ
  · right
    rw [hpair] at hLweq
    simp only [if_true] at hLweq
    refine ⟨by rw [hcirc z, hpair]; rfl, ?_⟩
    rw [← hLweq]
    exact hbZ

/-- The hypotheses of step (1) of `prop:sound` with `imp:window` discharged from the base library: the fields of
`ReconstructionHypotheses` other than `window`, plus `𝒫 ≠ ∅` and the box sizes of `lem:certify`(d)
(`2Λ - 2 ≤ (L_w - 1) A`, with `L_w = D'` for one circuit and `L_w = L_2` for two; paper/paper.tex and
`sec:params` item 7, `Λ = ⌊(L_w - 1) A / 2⌋ + 1`). -/
structure ReconstructionFacts : Prop where
  prime : ∀ p ∈ C.primes, p.Prime
  primes_nonempty : C.primes.Nonempty
  e_pos : 1 ≤ C.e
  guard : ∀ p ∈ C.primes, ∀ π : List Bool, π.length ≤ C.seedLength →
    2 * ∑ w, |C.walkWeight π w| < (p : ℤ) ^ C.e
  width : ∀ z, ∀ p ∈ C.primes, 2 * ((C.column z).hE : ℤ) - 1 ≤ p
  A_pos : ∀ z, 0 < (C.column z).A
  residual_le : ∀ z j c, |(C.column z).residual j c| ≤ C.G j
  residual_zero : ∀ z j, j ∉ (C.column z).circuits → ∀ c, (C.column z).residual j c = 0
  shape : ∀ z, ((C.column z).circuits = {0} ∧
      2 * ((C.column z).Lambda : ℤ) - 2 ≤
        ((NearCubicGates.ScalarWindow.window C.primes : ℤ) - 1) * (C.column z).A) ∨
    ((C.column z).circuits = {0, 1} ∧
      2 * ((C.column z).Lambda : ℤ) - 2 ≤
        ((pairWindow (NearCubicGates.ScalarWindow.window C.primes) : ℤ) - 1) * (C.column z).A)

/-- The reconstruction hypotheses follow from `ReconstructionFacts`, with `imp:window` proved
(`windowOne_of_frame`, `windowTwo_pairWindow`). -/
theorem ReconstructionFacts.toHypotheses {C : CellCall} (H : C.ReconstructionFacts) :
    C.ReconstructionHypotheses where
  prime := H.prime
  e_pos := H.e_pos
  guard := H.guard
  width := H.width
  A_pos := H.A_pos
  residual_le := H.residual_le
  residual_zero := H.residual_zero
  window := C.window_of_paper _ _ (windowOne_of_frame C.primes H.primes_nonempty H.prime)
    (windowTwo_pairWindow C.primes H.primes_nonempty H.prime) (fun p hp => (H.prime p hp).pos) H.A_pos H.shape

/-- **`prop:sound`** (Soundness for every witness), paper/paper.tex, with `imp:window` proved: for
every cell call, `|p̂ - p_true| ≤ κ̂`. The hypotheses are `imp:partition` (`PartitionAverage`), `lem:fourier`
(`FourierRows`), the sampler rule of `sec:params` (`SamplerBudget`) and the facts `ReconstructionFacts`
(`lem:identity`, the modulus bound of `lem:residue`, and parameter facts of `sec:params`). -/
theorem prop_sound_of_facts (p : ℚ) (hp : C.PartitionAverage p) (F : C.FourierRows) (hB : C.SamplerBudget)
    (H : C.ReconstructionFacts) :
    |C.run.1 - p| ≤ C.run.2 :=
  C.prop_sound p hp F hB H.toHypotheses

/-- A cell call *uses the parameters* `Pm` (`sec:params`) when its sampler, primes, exponent and column constants
are those of `Pm`: `N`, `Q`, `S = 2mℓ_f`, `η`, `I = 2|Θ|`, `𝒫`, `e`, `h_E`, `Λ`, `A`, and the circuit set
`𝒥 = {1, 2}` exactly for pair calls. -/
structure UsesParameters (Pm : Parameters) : Prop where
  N_eq : C.seed.N = Pm.N
  Q_eq : C.seed.Q = Pm.Q
  S_eq : C.seedLength = Pm.S
  eta_eq : C.η = Pm.eta
  I_eq : Pm.I = 2 * (Sampler.omega 4 (C.G 0) * Sampler.omega 4 (C.G 1))
  primes_eq : C.primes = Pm.primes
  e_eq : C.e = Pm.e
  hE_eq : ∀ z, (C.column z).hE = Pm.hE
  Lambda_eq : ∀ z, (C.column z).Lambda = Pm.Lambda
  A_eq : ∀ z, (C.column z).A = (Pm.A : ℤ)
  circuits_eq : ∀ z, (C.column z).circuits = if Pm.pair then {0, 1} else {0}

/-- The reconstruction facts for a cell call that uses the parameters, given the two facts about the call itself:
`lem:identity` (`|R_j| ≤ G_j`) and `R_j = 0` off `𝒥`. -/
theorem reconstructionFacts_of_parameters (Pm : Parameters) (U : C.UsesParameters Pm)
    (residual_le : ∀ z j c, |(C.column z).residual j c| ≤ C.G j)
    (residual_zero : ∀ z j, j ∉ (C.column z).circuits → ∀ c, (C.column z).residual j c = 0) :
    C.ReconstructionFacts where
  prime := U.primes_eq ▸ Pm.primes_prime
  primes_nonempty := U.primes_eq ▸ Pm.primes_nonempty
  e_pos := U.e_eq ▸ Pm.e_pos
  guard := C.guard_of_parameters Pm U.N_eq U.Q_eq U.S_eq U.primes_eq U.e_eq
  width := C.width_of_parameters Pm U.primes_eq U.hE_eq
  A_pos := fun z => by rw [U.A_eq z]; exact_mod_cast Pm.A_pos
  residual_le := residual_le
  residual_zero := residual_zero
  shape := C.shape_of_parameters Pm U.primes_eq U.circuits_eq U.Lambda_eq U.A_eq

/-- **`prop:sound` for a cell call that uses the parameters of `sec:params`**, paper/paper.tex:
`|p̂ - p_true| ≤ κ̂`. What remains to supply are the facts about the call on its cells: `imp:partition`
(`PartitionAverage`), `lem:fourier` (`FourierRows`), `lem:identity` (`residual_le`), `R_j = 0` off `𝒥`, and
`2 ≤ N ≤ Q`. -/
theorem prop_sound_of_parameters (Pm : Parameters) (U : C.UsesParameters Pm) (p : ℚ)
    (hp : C.PartitionAverage p) (F : C.FourierRows)
    (residual_le : ∀ z j c, |(C.column z).residual j c| ≤ C.G j)
    (residual_zero : ∀ z j, j ∉ (C.column z).circuits → ∀ c, (C.column z).residual j c = 0)
    (hN2 : 2 ≤ C.seed.N) (hNQ : C.seed.N ≤ C.seed.Q) :
    |C.run.1 - p| ≤ C.run.2 :=
  C.prop_sound_of_facts p hp F
    (C.samplerBudget_of_parameters Pm U.N_eq U.Q_eq U.eta_eq U.I_eq hN2 hNQ)
    (C.reconstructionFacts_of_parameters Pm U residual_le residual_zero)

end CellCall

end NearQuarticWires.Algorithm
