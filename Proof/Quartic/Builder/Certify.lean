import Proof.Quartic.Builder.Complete

/-!
# A column passes the certification tests when its values are small

Paper: proof of `prop:complete`, paragraph *Uncertified columns*, paper/paper.tex (its last
sentences); `lem:moments`; the tests `eq:testX`, `eq:testE`, `eq:testPhi`.

`certified_of_bounds` is the deterministic part of the paragraph: if at every structurally retained point
`X ≤ X_max/2`, and on every walk of mask one every digit has `|E| ≤ R_E` and the final error has `|φ| ≤ R_Φ` with
`√2 R_E < h_E` and `√2 R_Φ < Λ`, then the three strict tests pass. The proof is the converse of `lem:moments`
(`Walks.moment_complete`) on at most `N² ≤ 2^k` points and at most `N^{2m} ≤ 2^{mk}` walks.

`cellCall_certified` specializes it to the cell call of a call: the bounds are the conclusion of `lem:localize`
(`|E| ≤ mh`, `|φ| ≤ 172 m A T ℓ̄ / h`), and the margins come from `h_E ≥ 2mh` and the window condition
`eq:window`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicGates.Close.Interfaces

/-- A masked moment with a `0/1` mask is the moment of the masked values. -/
theorem maskedMoment_eq {V : Type*} [Fintype V] (K : ℕ) (hK : 1 ≤ K) (mask v : V → ℤ)
    (hmask : ∀ x, mask x = 0 ∨ mask x = 1) :
    Walks.maskedMoment K mask v = Walks.momentSum K (fun x => mask x * v x) := by
  unfold Walks.maskedMoment Walks.momentSum
  refine Finset.sum_congr rfl fun x _ => ?_
  show mask x * v x ^ (2 * K) = (mask x * v x) ^ (2 * K)
  rcases hmask x with h | h
  · rw [h, zero_mul, zero_mul, zero_pow (by omega)]
  · rw [h, one_mul, one_mul]

/-- The converse of `lem:moments` for a masked moment: if every value of mask one is at most `R'` and
`√2 R' < R`, on at most `2^K` indices, the strict test passes. -/
theorem maskedMoment_lt {V : Type*} [Fintype V] (K : ℕ) (hK : 1 ≤ K) (mask v : V → ℤ)
    (hmask : ∀ x, mask x = 0 ∨ mask x = 1) (R : ℕ) (R' : ℝ) (hcard : Fintype.card V ≤ 2 ^ K) (hR' : 0 ≤ R')
    (hb : ∀ x, mask x = 1 → ((v x).natAbs : ℝ) ≤ R') (hmargin : Real.sqrt 2 * R' < R) :
    Walks.maskedMoment K mask v < (R : ℤ) ^ (2 * K) := by
  rw [maskedMoment_eq K hK mask v hmask]
  refine Walks.moment_complete K hK _ R R' hcard hR' (fun x => ?_) hmargin
  rcases hmask x with h | h
  · simp [h, hR']
  · simpa [h] using hb x h

/-- **The certification tests pass on a column with small values** (`prop:complete`, paper/paper.tex). For column
data `D` on `N × N` cells with `N² ≤ 2^k`: if `X ≤ X_max / 2` at every point with `smask = 1`, and on every walk with
`mask_w = 1`, for every circuit of `𝒥` and every pattern with `κ_σ ≠ 0`, `|E_r| ≤ R_E` and `|φ| ≤ R_Φ`, where
`√2 R_E < h_E` and `√2 R_Φ < Λ`, then the column is certified. -/
theorem certified_of_bounds {N m J : ℕ} (hm : 0 < m) (k : ℕ) (hk : 1 ≤ k) (D : Walks.WalkData N m J)
    (hN : N * N ≤ 2 ^ k)
    (hX : ∀ q, D.structural q = true → 2 * D.X q ≤ D.Xmax)
    (RE RΦ : ℝ) (hRE : 0 ≤ RE) (hRΦ : 0 ≤ RΦ)
    (hE : ∀ j ∈ D.circuits, ∀ σ : Cycle.SignPattern m, Cycle.kappa m σ ≠ 0 → ∀ w : Cycle.Walk N m,
      Walks.walkMaskInt hm D.structural D.tau D.X w = 1 → ∀ r, ((D.E j σ w r).natAbs : ℝ) ≤ RE)
    (hΦ : ∀ j ∈ D.circuits, ∀ σ : Cycle.SignPattern m, Cycle.kappa m σ ≠ 0 → ∀ w : Cycle.Walk N m,
      Walks.walkMaskInt hm D.structural D.tau D.X w = 1 → ((D.phi hm j σ w).natAbs : ℝ) ≤ RΦ)
    (hEm : Real.sqrt 2 * RE < D.hE) (hΦm : Real.sqrt 2 * RΦ < D.Lambda) :
    Walks.ColumnCertificate hm k D := by
  classical
  have hsqrt : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- `eq:testX`
  have hpop : Walks.momentSum k (fun x : Walks.StructuralPoint D.structural => (D.X x.val : ℤ)) <
      ((D.Xmax + 1 : ℕ) : ℤ) ^ (2 * k) := by
    refine Walks.moment_complete k hk _ (D.Xmax + 1) ((D.Xmax : ℝ) / 2) ?_ (by positivity) ?_ ?_
    · calc Fintype.card (Walks.StructuralPoint D.structural) ≤ Fintype.card (Sampler.Cell N) :=
            Fintype.card_subtype_le _
        _ = N * N := by simp [Sampler.Cell, NearCubicWires.WireExponent3_5.Shared.Cell]
        _ ≤ 2 ^ k := hN
    · intro x
      have h := hX x.val x.property
      simp only [Int.natAbs_natCast]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : ((2 * D.X x.val : ℕ) : ℝ) ≤ D.Xmax := by exact_mod_cast h
      push_cast at this
      linarith
    · push_cast
      have h0 : (0 : ℝ) ≤ D.Xmax := Nat.cast_nonneg _
      nlinarith
  have hexact := Walks.testX_walkMaskPoly_exact hm D.structural k D.tau D.Xmax D.X hpop
  have hK : 1 ≤ m * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcardW : Fintype.card (Walks.StructuralWalk hm D.structural) ≤ 2 ^ (m * k) := by
    calc Fintype.card (Walks.StructuralWalk hm D.structural) ≤ Fintype.card (Cycle.Walk N m) :=
          Fintype.card_subtype_le _
      _ = (N * N) ^ m := by
          simp only [Cycle.Walk, Fintype.card_fun, Fintype.card_fin]
          rw [pow_mul, sq]
      _ ≤ (2 ^ k) ^ m := Nat.pow_le_pow_left hN m
      _ = 2 ^ (m * k) := by rw [← pow_mul, Nat.mul_comm]
  have hmask01 : ∀ w : Walks.StructuralWalk hm D.structural,
      Walks.walkMaskPoly hm D.structural D.tau D.Xmax D.X w.val = 0 ∨
        Walks.walkMaskPoly hm D.structural D.tau D.Xmax D.X w.val = 1 := by
    intro w
    rw [hexact]
    exact Walks.walkMaskInt_zero_or_one hm D.structural D.tau D.X w.val
  refine ⟨hpop, ?_, ?_⟩
  · intro j hj σ hσ r
    refine maskedMoment_lt (m * k) hK _ _ hmask01 D.hE RE hcardW hRE (fun w hw => ?_) hEm
    rw [hexact] at hw
    exact hE j hj σ hσ w.val hw r
  · intro j hj σ hσ
    refine maskedMoment_lt (m * k) hK _ _ hmask01 D.Lambda RΦ hcardW hRΦ (fun w hw => ?_) hΦm
    rw [hexact] at hw
    exact hΦ j hj σ hσ w.val hw

/-- `√2 · 172 < 487/2`, the constant comparison of the final tests (`prop:complete`, paper/paper.tex). -/
theorem sqrt_two_mul_le : Real.sqrt 2 * 172 < 487 / 2 := by
  have h : Real.sqrt 2 < 141422 / 100000 := by
    rw [show (141422 / 100000 : ℝ) = Real.sqrt ((141422 / 100000) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

section Margins

variable {p : Cells.Parameters}

/-- The final-error radius `R_Φ = 172 m A T ℓ̄ / h` of `lem:localize` (paper/paper.tex). -/
noncomputable def finalRadius : ℝ :=
  172 * 4 * (p.A : ℝ) * p.T * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h

/-- The final tests' margin from the window condition `eq:window` (paper/paper.tex):
`√2 · 172 m A T ℓ̄ / h < (487/2) m A T ℓ̄ / h < (L_w - 1) A / 2 < Λ`. -/
theorem finalRadius_margin {x : Cells.ParameterInput} (hs : Cells.ParameterRules x p)
    (hwin : 487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h < (p.Lw : ℚ) - 1) :
    Real.sqrt 2 * finalRadius (p := p) < p.Lambda := by
  have hm := hs.m_eq
  have hA : (0 : ℝ) < p.A := by exact_mod_cast Cells.ParameterRules.A_pos hs
  have hwr : 487 * 4 * (p.T : ℝ) * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h <
      (p.Lw : ℝ) - 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hwin
    rw [hm] at h
    push_cast at h
    exact h
  -- `Λ = ⌊(L_w - 1) A / 2⌋ + 1 > (L_w - 1) A / 2`
  have hΛ : ((p.Lw : ℝ) - 1) * p.A / 2 < p.Lambda := by
    rw [hs.Lambda_eq]
    have hLw : 1 ≤ p.Lw := by
      by_contra h
      push Not at h
      have : (p.Lw : ℝ) - 1 < 0 := by
        have : p.Lw = 0 := by omega
        rw [this]; norm_num
      have hpos : (0 : ℝ) ≤ 487 * 4 * (p.T : ℝ) *
          (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h := by
        have hT : (0 : ℝ) ≤ p.T := Nat.cast_nonneg _
        have hh : (0 : ℝ) ≤ p.h := Nat.cast_nonneg _
        have he : (0 : ℝ) ≤ (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) := by
          unfold NearCubicGates.Close.Counter.ellBar
          push_cast
          exact le_max_of_le_right (by positivity)
        positivity
      linarith
    have hdiv := Nat.lt_div_mul_add (a := (p.Lw - 1) * p.A) (show 0 < 2 by norm_num)
    have hcast : (((p.Lw - 1) * p.A : ℕ) : ℝ) < (((p.Lw - 1) * p.A / 2 * 2 + 2 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    push_cast [Nat.cast_sub hLw] at hcast ⊢
    linarith
  have hkey : Real.sqrt 2 * finalRadius (p := p) < 487 / 2 * ((p.A : ℝ) * p.T *
      (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h) * 4 := by
    unfold finalRadius
    have hx : (0 : ℝ) ≤ (p.A : ℝ) * p.T * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h := by
      have hT : (0 : ℝ) ≤ p.T := Nat.cast_nonneg _
      have hh : (0 : ℝ) ≤ p.h := Nat.cast_nonneg _
      have he : (0 : ℝ) ≤ (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) := by
        unfold NearCubicGates.Close.Counter.ellBar
        push_cast
        exact le_max_of_le_right (by positivity)
      positivity
    have hT1 : (1 : ℝ) ≤ p.T := by exact_mod_cast Cells.ParameterRules.T_pos hs
    have hpos : (0 : ℝ) < (p.A : ℝ) * p.T * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h ∨
        (p.A : ℝ) * p.T * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h = 0 :=
      (lt_or_eq_of_le hx).imp id Eq.symm
    rcases hpos with hpos | hzero
    · have := sqrt_two_mul_le
      have e1 : 172 * 4 * (p.A : ℝ) * p.T * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h =
          172 * 4 * ((p.A : ℝ) * p.T * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h) := by ring
      rw [e1]
      nlinarith
    · exfalso
      -- `ℓ̄ ≥ h²/(256 T) > 0` and `h > 0` force a positive value
      have hh : (0 : ℝ) < p.h := by exact_mod_cast (show 0 < p.h by have := hs.height; have := Cells.ParameterRules.T_pos hs; omega)
      have he : (0 : ℝ) < (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) := by
        unfold NearCubicGates.Close.Counter.ellBar
        push_cast
        exact lt_max_of_lt_right (by positivity)
      have : (0 : ℝ) < (p.A : ℝ) * p.T * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h := by
        positivity
      linarith
  calc Real.sqrt 2 * finalRadius (p := p) < 487 / 2 * ((p.A : ℝ) * p.T *
        (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h) * 4 := hkey
    _ = (487 * 4 * (p.T : ℝ) * (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) / p.h) * p.A / 2 := by
        ring
    _ ≤ ((p.Lw : ℝ) - 1) * p.A / 2 := by
        have := mul_le_mul_of_nonneg_right hwr.le hA.le
        linarith
    _ < p.Lambda := hΛ

/-- The digit tests' margin (`prop:complete`, paper/paper.tex): `√2 · m h < h_E`, from `h = ⌊h_E/(2m)⌋ ≥ 1`. -/
theorem digitRadius_margin {x : Cells.ParameterInput} (hs : Cells.ParameterRules x p) : Real.sqrt 2 * (4 * (p.h : ℝ)) < p.hE := by
  have hh1 : 1 ≤ p.h := by have := hs.height; have := Cells.ParameterRules.T_pos hs; omega
  have hmh : 8 * p.h ≤ p.hE := by
    rw [hs.h_eq, hs.m_eq]
    have := Nat.div_mul_le_self p.hE 8
    omega
  have hsqrt : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ≤ p.h := by exact_mod_cast hh1
  have h2 : (8 * p.h : ℝ) ≤ p.hE := by exact_mod_cast hmh
  nlinarith

end Margins

section Cell

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- **A column of the cell call is certified when the bad events of the paragraph *Uncertified columns* fail**
(paper/paper.tex): if `X < X_max/2` at every point with `smask = 1` (event (i) fails) and the
conclusion of `lem:localize` holds on every walk with `mask_w = 1` (event (iii) fails), then, under the window
condition, the three tests pass. -/
theorem cellCall_certified (w : List Bool) (z : Fin (cellCall c hs w).ncol)
    (hwin : 487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h < (p.Lw : ℚ) - 1)
    (hX : ∀ q, ((cellCall c hs w).column z).structural q = true →
      2 * ((cellCall c hs w).column z).X q ≤ p.Xmax)
    (hloc : ∀ j ∈ ((cellCall c hs w).column z).circuits, ∀ σ : Cycle.SignPattern Algorithm.traceOrder,
      Cycle.kappa Algorithm.traceOrder σ ≠ 0 → ∀ walk : Cycle.Walk hs.seedParameters.N Algorithm.traceOrder,
      (cellCall c hs w).walkMask z walk = 1 →
      (∀ r, (((cellCall c hs w).column z).E j σ walk r).natAbs ≤ 4 * p.h) ∧
      ((((cellCall c hs w).column z).phi Algorithm.traceOrder_pos j σ walk).natAbs : ℝ) ≤ finalRadius (p := p)) :
    (cellCall c hs w).Certified z := by
  have hk : 1 ≤ p.k := by
    have := Cells.ParameterRules.N_ge_two hs
    rw [hs.N_eq] at this
    by_contra h
    push Not at h
    have : p.k / 2 = 0 := by omega
    simp_all
  have hN : hs.seedParameters.N * hs.seedParameters.N ≤ 2 ^ p.k := by
    rw [Cells.ParameterRules.seed_N hs, ← sq, Cells.ParameterRules.N_square hs]
  have hR0 : (0 : ℝ) ≤ finalRadius (p := p) := by
    unfold finalRadius
    have he : (0 : ℝ) ≤ (NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T : ℝ) := by
      unfold NearCubicGates.Close.Counter.ellBar
      push_cast
      exact le_max_of_le_right (by positivity)
    positivity
  refine certified_of_bounds Algorithm.traceOrder_pos p.k hk ((cellCall c hs w).column z) hN hX
    (4 * (p.h : ℝ)) (finalRadius (p := p)) (by positivity) hR0 ?_ ?_ (digitRadius_margin hs)
    (finalRadius_margin hs hwin)
  · intro j hj σ hσ walk hw r
    have := (hloc j hj σ hσ walk hw).1 r
    exact_mod_cast this
  · intro j hj σ hσ walk hw
    exact (hloc j hj σ hσ walk hw).2

end Cell

end NearQuarticWires.Builder
