import Proof.Quartic.Reconstruct.Gather

/-!
# The box of a system in natural arithmetic

Paper: `lem:certify`(d), paper/paper.tex, and Step 3.

The coordinate `j ∈ 𝒥` of the box `Bx(δ)` is the integer interval
`[max(⌈(M_1K - Λ + 1)/A⌉, -B), min(⌊(M_1K + Λ - 1)/A⌋, B)]` with `K = K(δ^{(j)})` the digit value of `δ^{(j)}` under
the rates and `B = 2mG_j`. A program on natural numbers computes it as follows.

* `reconstruct_split`: Horner's scheme is linear in the digits, so `K = K⁺ - K⁻` with `K^±` Horner's scheme on the
  positive and negative parts of the digits (`hornerN`, natural numbers).
* `intervalList_box`: shifted by `B`, the interval starts at `lo' = (M_1K⁺ + A + AB ∸ (M_1K⁻ + Λ)) / A` and has
  `min((M_1K⁺ + (Λ - 1) + AB + A ∸ M_1K⁻) / A, 2B + 1) ∸ lo'` points (truncated subtraction and natural division).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

/-- Horner's scheme `d_0, d_0 a_0 + d_1, (d_0 a_0 + d_1) a_1 + d_2, …` for natural digits and rates. -/
def hornerN (rate : ℕ → ℕ) (dig : ℕ → ℕ) : ℕ → ℕ
  | 0 => dig 0
  | i + 1 => rate i * hornerN rate dig i + dig (i + 1)

/-- **Horner's scheme is linear in the digits**: with nonnegative rates, the digit value of a signed digit
sequence is the difference of the digit values of its positive and negative parts. -/
theorem reconstruct_split (rate : ℕ → ℕ) (d : ℕ → ℤ) : ∀ J,
    NearCubicGates.CountingCore.reconstruct (fun i => (rate i : ℤ)) d J =
      (hornerN rate (fun i => (d i).toNat) J : ℤ) - hornerN rate (fun i => (-d i).toNat) J
  | 0 => by
    simp only [NearCubicGates.CountingCore.reconstruct, hornerN]
    exact (Int.toNat_sub_toNat_neg (d 0)).symm
  | J + 1 => by
    simp only [NearCubicGates.CountingCore.reconstruct, hornerN]
    rw [reconstruct_split rate d J]
    have h := Int.toNat_sub_toNat_neg (d (J + 1))
    push_cast
    linear_combination (-1 : ℤ) * h

theorem ediv_neg_of_neg {x a : ℤ} (hx : x < 0) (ha : 0 < a) : x / a < 0 :=
  Int.ediv_neg_of_neg_of_pos hx ha

/-- `max (x / A) 0` is the natural quotient of the truncated difference. -/
theorem max_ediv_zero (X Y A : ℕ) (hA : 0 < A) :
    max (((X : ℤ) - Y) / A) 0 = (((X - Y) / A : ℕ) : ℤ) := by
  by_cases h : Y ≤ X
  · have h1 : ((X : ℤ) - Y) = ((X - Y : ℕ) : ℤ) := by push_cast [h]; ring
    rw [h1, ← Int.natCast_div]
    exact max_eq_left (Int.natCast_nonneg _)
  · have h1 : X - Y = 0 := by omega
    rw [h1, Nat.zero_div, Nat.cast_zero]
    exact max_eq_right (ediv_neg_of_neg (by omega) (by exact_mod_cast hA)).le

/-- **The box coordinate in natural arithmetic.** -/
theorem intervalList_box (M A L B Hp Hn : ℕ) (hA : 1 ≤ A) (hL : 1 ≤ L) :
    intervalList
        (max (NearCubicGates.ScoreBox.lower ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) (-(B : ℤ)))
        (min (NearCubicGates.ScoreBox.upper ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) B) =
      (List.range (min ((M * Hp + (L - 1) + A * B + A - M * Hn) / A) (2 * B + 1) -
          (M * Hp + A + A * B - (M * Hn + L)) / A)).map
        fun i : ℕ => (((M * Hp + A + A * B - (M * Hn + L)) / A : ℕ) : ℤ) - B + (i : ℤ) := by
  have hA' : (0 : ℤ) < A := by exact_mod_cast hA
  have hAne : (A : ℤ) ≠ 0 := ne_of_gt hA'
  set lo' := (M * Hp + A + A * B - (M * Hn + L)) / A with hlo'
  set hp := (M * Hp + (L - 1) + A * B + A - M * Hn) / A with hhp
  -- the lower end, shifted by `B`
  have hlow : max (NearCubicGates.ScoreBox.lower ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) (-(B : ℤ)) =
      (lo' : ℤ) - B := by
    unfold NearCubicGates.ScoreBox.lower NearCubicGates.ScoreBox.ceilDiv
    have e1 : (0 : ℤ) + ((M : ℤ) * ((Hp : ℤ) - Hn) - L + 1 + A - 1) / A + B =
        (((M * Hp + A + A * B : ℕ) : ℤ) - ((M * Hn + L : ℕ) : ℤ)) / A := by
      rw [zero_add, ← Int.add_mul_ediv_right _ _ hAne]
      congr 1
      push_cast
      ring
    have e2 := max_ediv_zero (M * Hp + A + A * B) (M * Hn + L) A hA
    rw [← e1] at e2
    rw [hlo']
    omega
  -- the upper end plus one, shifted by `B`
  have hup : min (NearCubicGates.ScoreBox.upper ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) B + 1 + B =
      min ((((M * Hp + (L - 1) + A * B + A : ℕ) : ℤ) - ((M * Hn : ℕ) : ℤ)) / A) (2 * B + 1) := by
    unfold NearCubicGates.ScoreBox.upper
    have e1 : (0 : ℤ) + ((M : ℤ) * ((Hp : ℤ) - Hn) + L - 1) / A + 1 + B =
        (((M * Hp + (L - 1) + A * B + A : ℕ) : ℤ) - ((M * Hn : ℕ) : ℤ)) / A := by
      rw [zero_add, show ((M : ℤ) * ((Hp : ℤ) - Hn) + L - 1) / A + 1 + B =
        ((M : ℤ) * ((Hp : ℤ) - Hn) + L - 1) / A + (1 + B) by ring, ← Int.add_mul_ediv_right _ _ hAne]
      congr 1
      push_cast [Nat.cast_sub hL]
      ring
    rw [← e1]
    omega
  unfold intervalList
  have hlen : (min (NearCubicGates.ScoreBox.upper ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) B + 1 -
      max (NearCubicGates.ScoreBox.lower ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) (-(B : ℤ))).toNat =
      min hp (2 * B + 1) - lo' := by
    have h1 : min (NearCubicGates.ScoreBox.upper ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) B + 1 -
        max (NearCubicGates.ScoreBox.lower ((M : ℤ) * ((Hp : ℤ) - Hn)) A 0 L) (-(B : ℤ)) =
        min ((((M * Hp + (L - 1) + A * B + A : ℕ) : ℤ) - ((M * Hn : ℕ) : ℤ)) / A) (2 * B + 1) - lo' := by
      rw [hlow, ← hup]
      ring
    rw [h1]
    by_cases hc : M * Hn ≤ M * Hp + (L - 1) + A * B + A
    · have h2 : (((M * Hp + (L - 1) + A * B + A : ℕ) : ℤ) - ((M * Hn : ℕ) : ℤ)) / A = (hp : ℤ) := by
        rw [hhp, Int.natCast_div]
        congr 1
        push_cast [hc]
        ring
      rw [h2]
      have h3 : (min (hp : ℤ) (2 * B + 1)) = ((min hp (2 * B + 1) : ℕ) : ℤ) := by push_cast; rfl
      rw [h3]
      omega
    · have h2 : (((M * Hp + (L - 1) + A * B + A : ℕ) : ℤ) - ((M * Hn : ℕ) : ℤ)) / A < 0 :=
        ediv_neg_of_neg (by push_cast at hc ⊢; omega) hA'
      have h4 : hp = 0 := by rw [hhp]; rw [show M * Hp + (L - 1) + A * B + A - M * Hn = 0 by omega]; simp
      rw [h4]
      have : min ((((M * Hp + (L - 1) + A * B + A : ℕ) : ℤ) - ((M * Hn : ℕ) : ℤ)) / A) (2 * B + 1) < 0 :=
        lt_of_le_of_lt (min_le_left _ _) h2
      omega
  rw [hlen, hlow]

end NearQuarticWires.Reconstruct

namespace NearQuarticWires.Reconstruct

open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

theorem reconstruct_congr (r1 r2 : ℕ → ℤ) (d : ℕ → ℤ) : ∀ J, (∀ i < J, r1 i = r2 i) →
    NearCubicGates.CountingCore.reconstruct r1 d J = NearCubicGates.CountingCore.reconstruct r2 d J
  | 0, _ => rfl
  | J + 1, h => by
    simp only [NearCubicGates.CountingCore.reconstruct]
    rw [reconstruct_congr r1 r2 d J (fun i hi => h i (by omega)), h J (by omega)]

/-- The rates of the algorithm are the factors of the parameter record (`sec:params`). -/
theorem rate_eq_factors (q : ChildRequest B1 B2) (i : ℕ) (hi : i < q.cellCall.J) :
    ((Builder.algorithmParameters q.call (rules q)).rate i : ℤ) = ((q.selected.1.factors.getD i 0 : ℕ) : ℤ) := by
  have hJ : q.cellCall.J = q.selected.1.J - 1 := rfl
  rw [hJ] at hi
  rw [(rules q).factors_eq]
  unfold NearCubicGates.Close.Counter.chainFactors
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  rfl

/-- The positive part (`s = true`) or the negative part (`s = false`) of a digit of `δ^{(j)}`, extended by zeros. -/
noncomputable def digitPart (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2)
    (s : Bool) (i : ℕ) : ℕ :=
  if s then (NearCubicGates.CertifiedScoreSupport.extendDigits (δ j) i).toNat
  else (-NearCubicGates.CertifiedScoreSupport.extendDigits (δ j) i).toNat

/-- **The box coordinate of a circuit from the parameters, in natural arithmetic** (`lem:certify`(d)): with
`K^± = hornerN (factors) (digitPart ±)`, `B = 2mG_j`, `lo' = (M_1K⁺ + A + AB ∸ (M_1K⁻ + Λ)) / A` and
`hp = (M_1K⁺ + (Λ - 1) + AB + A ∸ M_1K⁻) / A`, the coordinate list is `lo' - B, lo' - B + 1, …` with
`min hp (2B + 1) ∸ lo'` entries. -/
theorem boxAxisOf_eq (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (j : Fin 2)
    (hj : j ∈ Builder.circuitSet q.call) :
    let M := q.selected.1.M1
    let A := q.selected.1.A
    let L := q.selected.1.Lambda
    let B := 2 * Algorithm.traceOrder * Builder.occurrences q.call j
    let Hp := hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j true) q.cellCall.J
    let Hn := hornerN (fun i => q.selected.1.factors.getD i 0) (digitPart q δ j false) q.cellCall.J
    boxAxisOf q δ j = (List.range (min ((M * Hp + (L - 1) + A * B + A - M * Hn) / A) (2 * B + 1) -
          (M * Hp + A + A * B - (M * Hn + L)) / A)).map
        fun i : ℕ => (((M * Hp + A + A * B - (M * Hn + L)) / A : ℕ) : ℤ) - B + (i : ℤ) := by
  intro M A L B Hp Hn
  have H := reconstructionHypotheses_of_dispatch q.dispatched q.witness
  have hpos : 0 < q.cellCall.ncol := Nat.two_pow_pos _
  have hA : 1 ≤ A := by
    have h := H.A_pos ⟨0, hpos⟩
    change (0 : ℤ) < (q.selected.1.A : ℤ) at h
    exact_mod_cast h
  have hL : 1 ≤ L := by
    show 1 ≤ q.selected.1.Lambda
    rw [(rules q).Lambda_eq]
    omega
  have hK : Walks.digitValue (fun i => ((Builder.algorithmParameters q.call (rules q)).rate i : ℤ)) (δ j) =
      (Hp : ℤ) - Hn := by
    unfold Walks.digitValue
    rw [reconstruct_congr _ (fun i => ((q.selected.1.factors.getD i 0 : ℕ) : ℤ)) _ _
      (fun i hi => rate_eq_factors q i hi), reconstruct_split]
    rfl
  have hbox := intervalList_box M A L B Hp Hn hA hL
  unfold boxAxisOf
  rw [if_pos hj]
  convert hbox using 3 <;> first
    | rw [hK]
    | (simp only [B]; push_cast; ring)

end NearQuarticWires.Reconstruct

namespace NearQuarticWires.Reconstruct

theorem hornerN_congr (r1 r2 d1 d2 : ℕ → ℕ) : ∀ N, (∀ i < N, r1 i = r2 i) → (∀ i ≤ N, d1 i = d2 i) →
    hornerN r1 d1 N = hornerN r2 d2 N
  | 0, _, hd => by simp [hornerN, hd 0 le_rfl]
  | N + 1, hr, hd => by
    simp only [hornerN]
    rw [hornerN_congr r1 r2 d1 d2 N (fun i hi => hr i (by omega)) (fun i hi => hd i (by omega)), hr N (by omega),
      hd (N + 1) le_rfl]

/-- A crude bound on Horner's scheme: `hornerN a d N ≤ (D + 1)(R + 1)^N` when every digit is at most `D` and every
rate at most `R`. -/
theorem hornerN_le (r d : ℕ → ℕ) (R D : ℕ) (hr : ∀ i, r i ≤ R) (hd : ∀ i, d i ≤ D) :
    ∀ N, hornerN r d N ≤ (D + 1) * (R + 1) ^ N
  | 0 => by simp [hornerN]; exact (hd 0).trans (by omega)
  | N + 1 => by
    simp only [hornerN]
    have ih := hornerN_le r d R D hr hd N
    have h1 : r N * hornerN r d N ≤ R * ((D + 1) * (R + 1) ^ N) := Nat.mul_le_mul (hr N) ih
    have h2 := hd (N + 1)
    have h3 : 1 ≤ (R + 1) ^ N := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    nlinarith

end NearQuarticWires.Reconstruct
