import Proof.Quartic.Program.Stages
import Proof.Quartic.Machine.Output
import Proof.Gates.CounterAsm.Main

/-!
# The output of the counter: dyadic endpoints and output words of linear length

Paper: `prop:time`, paper/paper.tex (dyadic outputs of `O(n)` bits) and Step 5 of
`sec:algorithm` (outward rounding to multiples of `2^{-n}`).

Every value of the counter has the form `(z₁ / 2^{n+1}, z₂ / 2^{n+1})` with integers `|zᵢ| ≤ 2^{n+5}`
(`value_scaled`): the sound default `(1/2, 1/2)`, the exact value of a call with `W = 0`, and the rounded interval
`(p̂, κ̂)` of Step 5, whose endpoints satisfy `|Lo|, |Hi| ≤ 8` because every sampled mean lies in
`[0, 1]` and `2 M_F η = β/8` (`lower_mem`, `upper_mem`). Hence the denominators divide `2^{n+1}` (`admittedValue_den`) and
the output word has length at most `8n + 50` (`admittedValue_outputWord_length`).

The section *Normalized calls* records that a normalized call of `Transfer.Admitted4` is a normalized call of
`Call.Admitted` (unit top coefficients give `W ≤ ` the wire count, `topWeight_le_wires`), so its call word has
polynomial length (`callWord_length_le`, from `Proof.Gates.CounterAsm.Main`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-! ## Scaled dyadic rationals -/

/-- `q · 2^{n+1}` is an integer of absolute value at most `2^{n+5}`. -/
def Scaled (n : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, q * 2 ^ (n + 1) = z ∧ z.natAbs ≤ 2 ^ (n + 5)

theorem Scaled.den {n : ℕ} {q : ℚ} (h : Scaled n q) : (q * 2 ^ (n + 1)).den = 1 := by
  obtain ⟨z, hz, -⟩ := h
  rw [hz]
  rfl

theorem scaled_zero (n : ℕ) : Scaled n 0 := ⟨0, by simp, by simp⟩

theorem scaled_half (n : ℕ) : Scaled n (1 / 2) := by
  refine ⟨2 ^ n, by rw [pow_succ]; push_cast; ring, ?_⟩
  rw [Int.natAbs_pow]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem scaled_one (n : ℕ) : Scaled n 1 := by
  refine ⟨2 ^ (n + 1), by push_cast; ring, ?_⟩
  rw [Int.natAbs_pow]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem scaled_bitQ (n : ℕ) (b : Bool) : Scaled n (Builder.bitQ b) := by
  cases b
  · simpa [Builder.bitQ] using scaled_zero n
  · simpa [Builder.bitQ] using scaled_one n

/-- An integer `z` with `|z| ≤ 2^{m+4}` over `2^m` prints in at most `4m + 21` cells. -/
theorem ratWord_length_le_of_scaled (q : ℚ) (m : ℕ) (z : ℤ) (h : q * 2 ^ m = z) (hz : z.natAbs ≤ 2 ^ (m + 4)) :
    (ratWord q).length ≤ 4 * m + 21 := by
  have hb : ((2 ^ m : ℕ) : ℤ) ≠ 0 := by positivity
  have hq : q = Rat.divInt z ((2 ^ m : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    have h2 : (2 : ℚ) ^ m ≠ 0 := by positivity
    push_cast
    rw [← h]
    field_simp
  have hnum : q.num.natAbs ≤ 2 ^ (m + 4) := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · rw [hq, hz0]; simp
    · rw [hq]
      have h1 := Rat.num_dvd z hb
      have h2 := Int.natAbs_dvd_natAbs.mpr h1
      exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hz0) h2).trans hz
  have hden : q.den ≤ 2 ^ m := by
    rw [hq]
    have h1 := Rat.den_dvd z ((2 ^ m : ℕ) : ℤ)
    have h2 : (Rat.divInt z ((2 ^ m : ℕ) : ℤ)).den ∣ 2 ^ m := by exact_mod_cast h1
    exact Nat.le_of_dvd (by positivity) h2
  have hlt : ∀ v k, v ≤ 2 ^ k → v < 2 ^ (k + 1) := fun v k hv => by
    have := @Nat.one_le_two_pow k
    rw [pow_succ]; omega
  have b1 := NearCubicGates.Close.CounterAsm.nbl_le_of_lt' (hlt _ _ hnum) (by omega)
  have b2 := NearCubicGates.Close.CounterAsm.nbl_le_of_lt' (hlt _ _ hden) (by omega)
  have b0 : natBitLength (if q.num < 0 then 1 else 0) ≤ 1 :=
    NearCubicGates.Close.CounterAsm.nbl_le_of_lt' (k := 1) (by split_ifs <;> norm_num) le_rfl
  simp only [ratWord, NearCubicGates.Close.Interfaces.intWord, List.length_append,
    NearCubicGates.Close.CounterAsm.natWord_len']
  omega

theorem Scaled.ratWord_length {n : ℕ} {q : ℚ} (h : Scaled n q) : (ratWord q).length ≤ 4 * n + 25 := by
  obtain ⟨z, hz, hb⟩ := h
  have := ratWord_length_le_of_scaled q (n + 1) z hz (by rw [show n + 1 + 4 = n + 5 by omega]; exact hb)
  omega

/-! ## Step 5: the rounded interval -/

/-- Step 5, `prop:sound`: with `|Lo|, |Hi| ≤ 8`, both rounded values are scaled dyadic rationals. -/
theorem centerRadius_scaled (n : ℕ) (lo hi : ℚ) (hlo : |lo| ≤ 8) (hhi : |hi| ≤ 8) :
    Scaled n (Algorithm.centerRadius n lo hi).1 ∧ Scaled n (Algorithm.centerRadius n lo hi).2 := by
  have hp : (0 : ℚ) < 2 ^ n := by positivity
  set F := ⌊lo * 2 ^ n⌋ with hF
  set G := ⌈hi * 2 ^ n⌉ with hG
  have hF1 : (F : ℚ) ≤ lo * 2 ^ n := Int.floor_le _
  have hF2 : lo * 2 ^ n < F + 1 := Int.lt_floor_add_one _
  have hG1 : hi * 2 ^ n ≤ G := Int.le_ceil _
  have hG2 : (G : ℚ) < hi * 2 ^ n + 1 := Int.ceil_lt_add_one _
  have hl := abs_le.mp hlo
  have hh := abs_le.mp hhi
  have hpow : (2 : ℚ) ^ (n + 5) = 32 * 2 ^ n := by rw [pow_add]; norm_num; ring
  have hone : (1 : ℚ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have key : ∀ z : ℤ, (|(z : ℚ)| ≤ 2 ^ (n + 5)) → z.natAbs ≤ 2 ^ (n + 5) := by
    intro z hz
    have h1 : |z| ≤ (2 : ℤ) ^ (n + 5) := by
      rw [← Int.cast_abs] at hz
      exact_mod_cast hz
    have h2 : (z.natAbs : ℤ) ≤ 2 ^ (n + 5) := by rw [Int.natCast_natAbs]; exact h1
    exact_mod_cast h2
  have hc : (Algorithm.centerRadius n lo hi).1 * 2 ^ (n + 1) = ((F + G : ℤ) : ℚ) := by
    have := Machine.roundedInterval_center_scaled n lo hi
    exact this
  have hr : (Algorithm.centerRadius n lo hi).2 * 2 ^ (n + 1) = ((G - F : ℤ) : ℚ) := by
    have := Machine.roundedInterval_radius_scaled n lo hi
    exact this
  refine ⟨⟨F + G, hc, key _ ?_⟩, ⟨G - F, hr, key _ ?_⟩⟩
  · push_cast
    rw [abs_le, hpow]
    constructor <;> nlinarith
  · push_cast
    rw [abs_le, hpow]
    constructor <;> nlinarith

namespace CellBounds

open Algorithm Algorithm.CellCall

variable (C : CellCall)

theorem bitInt_mem (b : Bool) : 0 ≤ bitInt b ∧ bitInt b ≤ 1 := by
  cases b <;> simp [bitInt]

theorem pointMask_mem (z : Fin C.ncol) (x : Sampler.Cell C.seed.N) :
    0 ≤ C.pointMask z x ∧ C.pointMask z x ≤ 1 := by
  unfold pointMask Mask.mask
  split_ifs <;> norm_num

/-- A mean over `Q` samples of integers in `{0, 1}` lies in `[0, 1]`. -/
theorem mean_mem {Q : ℕ} (f : Fin Q → ℤ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) :
    0 ≤ ((∑ j, f j : ℤ) : ℚ) / Q ∧ ((∑ j, f j : ℤ) : ℚ) / Q ≤ 1 := by
  have h0 : 0 ≤ (∑ j, f j : ℤ) := Finset.sum_nonneg fun j _ => (hf j).1
  have h1 : (∑ j, f j : ℤ) ≤ Q := by
    calc (∑ j, f j : ℤ) ≤ ∑ _j : Fin Q, (1 : ℤ) := Finset.sum_le_sum fun j _ => (hf j).2
      _ = Q := by simp
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ; simp
  · have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
    refine ⟨div_nonneg (by exact_mod_cast h0) hQ'.le, (div_le_one hQ').mpr (by exact_mod_cast h1)⟩

theorem sampledAccept_mem (S : Fin C.seed.Q → Sampler.Cell C.seed.N) (z : Fin C.ncol) :
    0 ≤ C.sampledAccept S z ∧ C.sampledAccept S z ≤ 1 := by
  unfold sampledAccept
  rw [← Int.cast_sum]
  apply mean_mem
  intro j
  have h1 := bitInt_mem (C.pred z (S j))
  have h2 := pointMask_mem C z (S j)
  constructor <;> nlinarith

theorem sampledMask_mem (S : Fin C.seed.Q → Sampler.Cell C.seed.N) (z : Fin C.ncol) :
    0 ≤ C.sampledMask S z ∧ C.sampledMask S z ≤ 1 := by
  unfold sampledMask
  exact mean_mem _ fun j => pointMask_mem C z (S j)

theorem card_le (Z : Finset (Fin C.ncol)) : (Z.card : ℚ) ≤ C.ncol := by
  have := Finset.card_le_univ Z
  rw [Fintype.card_fin] at this
  exact_mod_cast this

/-- Step 5 of `sec:algorithm`: `|Lo| ≤ 8` (indeed `Lo ∈ [-1, 1]`) when `0 ≤ 2 M_F η ≤ 1`. -/
theorem lower_mem (Z : Finset (Fin C.ncol)) (S : Fin C.seed.Q → Sampler.Cell C.seed.N) (hncol : 0 < C.ncol)
    (hMF : 0 ≤ 2 * (C.MF : ℚ) * C.η ∧ 2 * (C.MF : ℚ) * C.η ≤ 1) : |C.lower Z S| ≤ 8 := by
  unfold lower
  have hn : (0 : ℚ) < C.ncol := by exact_mod_cast hncol
  have hZ := card_le C Z
  have hs0 : 0 ≤ ∑ z ∈ Z, C.sampledAccept S z := Finset.sum_nonneg fun z _ => (sampledAccept_mem C S z).1
  have hs1 : ∑ z ∈ Z, C.sampledAccept S z ≤ Z.card := by
    calc ∑ z ∈ Z, C.sampledAccept S z ≤ ∑ _z ∈ Z, (1 : ℚ) := Finset.sum_le_sum fun z _ => (sampledAccept_mem C S z).2
      _ = Z.card := by simp
  have hc0 : (0 : ℚ) ≤ Z.card := by positivity
  have hm : 2 * (C.MF : ℚ) * Z.card * C.η = (2 * C.MF * C.η) * Z.card := by ring
  rw [abs_le, hm]
  constructor
  · rw [le_div_iff₀ hn]; nlinarith
  · rw [div_le_iff₀ hn]; nlinarith

/-- Step 5, `sec:analysis`: `|Hi| ≤ 8` (indeed `Hi ∈ [0, 5]`) when `0 ≤ 2 M_F η ≤ 1` and `0 ≤ η ≤ 1`. -/
theorem upper_mem (Z : Finset (Fin C.ncol)) (S : Fin C.seed.Q → Sampler.Cell C.seed.N) (hncol : 0 < C.ncol)
    (hMF : 0 ≤ 2 * (C.MF : ℚ) * C.η ∧ 2 * (C.MF : ℚ) * C.η ≤ 1) (hη : 0 ≤ C.η ∧ C.η ≤ 1) :
    |C.upper Z S| ≤ 8 := by
  unfold upper
  have hn : (0 : ℚ) < C.ncol := by exact_mod_cast hncol
  have hZ := card_le C Z
  have hs0 : 0 ≤ ∑ z ∈ Z, (C.sampledAccept S z + 1 - C.sampledMask S z) :=
    Finset.sum_nonneg fun z _ => by
      have := sampledAccept_mem C S z; have := sampledMask_mem C S z; linarith
  have hs1 : ∑ z ∈ Z, (C.sampledAccept S z + 1 - C.sampledMask S z) ≤ 2 * Z.card := by
    calc ∑ z ∈ Z, (C.sampledAccept S z + 1 - C.sampledMask S z) ≤ ∑ _z ∈ Z, (2 : ℚ) :=
          Finset.sum_le_sum fun z _ => by
            have := sampledAccept_mem C S z; have := sampledMask_mem C S z; linarith
      _ = 2 * Z.card := by simp; ring
  have hc0 : (0 : ℚ) ≤ Z.card := by positivity
  have hm : (2 * (C.MF : ℚ) + 1) * Z.card * C.η = (2 * C.MF * C.η + C.η) * Z.card := by ring
  rw [abs_le, hm]
  constructor
  · rw [le_div_iff₀ hn]; nlinarith
  · rw [div_le_iff₀ hn]; nlinarith

/-- The algorithm's output (`sec:algorithm`): scaled dyadic endpoints when `0 ≤ 2 M_F η ≤ 1` and `0 ≤ η ≤ 1`. -/
theorem run_scaled (hncol : 0 < C.ncol) (hMF : 0 ≤ 2 * (C.MF : ℚ) * C.η ∧ 2 * (C.MF : ℚ) * C.η ≤ 1)
    (hη : 0 ≤ C.η ∧ C.η ≤ 1) : Scaled C.n C.run.1 ∧ Scaled C.n C.run.2 := by
  classical
  unfold run
  split_ifs
  · exact centerRadius_scaled C.n _ _ (lower_mem C _ _ hncol hMF) (upper_mem C _ _ hncol hMF hη)
  · exact ⟨scaled_half _, scaled_half _⟩

end CellBounds

/-! ## The value of the counting algorithm -/

/-- `sec:params`: `2 M_F η = β/8 ∈ [0, 1]` and `η ∈ [0, 1]` for the selected parameters. -/
theorem eta_bounds (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (Builder.callInput c) p) :
    (0 ≤ 2 * (p.MF : ℚ) * p.eta ∧ 2 * (p.MF : ℚ) * p.eta ≤ 1) ∧ (0 ≤ p.eta ∧ p.eta ≤ 1) := by
  obtain ⟨_, _, _, _, hb0, hb1, _⟩ := hs.input_valid
  have he := hs.eta_eq
  change 0 < c.radius at hb0
  change c.radius ≤ 1 / 16 at hb1
  change p.eta = c.radius / (16 * p.MF) at he
  rw [he]
  rcases Nat.eq_zero_or_pos p.MF with h0 | h0
  · rw [h0]; simp
  · have hM : (1 : ℚ) ≤ p.MF := by exact_mod_cast h0
    have hM0 : (0 : ℚ) < 16 * p.MF := by positivity
    have e1 : 2 * (p.MF : ℚ) * (c.radius / (16 * p.MF)) = c.radius / 8 := by field_simp; ring
    rw [e1]
    refine ⟨⟨by positivity, by linarith⟩, by positivity, ?_⟩
    rw [div_le_one hM0]
    nlinarith

/-- **Every value of the counting algorithm is a pair of scaled dyadic rationals** (`prop:time`):
`(p̂, κ̂) = (z₁, z₂) / 2^{n+1}` with `|zᵢ| ≤ 2^{n+5}`, on every call and every witness. -/
theorem value_scaled (c : Call) (w : List Bool) :
    Scaled c.n (Builder.value c w).1 ∧ Scaled c.n (Builder.value c w).2 := by
  classical
  unfold Builder.value
  split_ifs with hc hn hW
  · exact ⟨scaled_half _, scaled_half _⟩
  · unfold Builder.closedValue
    split
    · exact ⟨scaled_bitQ _ _, scaled_zero _⟩
    · exact ⟨scaled_bitQ _ _, scaled_zero _⟩
    · split_ifs
      · exact ⟨scaled_half _, scaled_zero _⟩
      · exact ⟨scaled_bitQ _ _, scaled_zero _⟩
  · split
    · exact ⟨scaled_half _, scaled_half _⟩
    · rename_i p h
      have hs := Cells.prepare_spec _ p h
      obtain ⟨hMF, hη⟩ := eta_bounds c hs
      exact CellBounds.run_scaled (Builder.cellCall c hs w) (Nat.two_pow_pos _) hMF hη
  · exact ⟨scaled_half _, scaled_half _⟩

theorem admittedValue_scaled (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    Scaled c.n (admittedValue B1 B2 Builder.value c w).1 ∧ Scaled c.n (admittedValue B1 B2 Builder.value c w).2 := by
  by_cases h : Transfer.Admitted4 B1 B2 c
  · rw [admittedValue_of_admitted _ h]; exact value_scaled c w
  · rw [admittedValue_of_not_admitted _ h]; exact ⟨scaled_half _, scaled_half _⟩

/-- `thm:counter` and `prop:time`: dyadic endpoints with denominators dividing `2^{n+1}`. -/
theorem admittedValue_den (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    ((admittedValue B1 B2 Builder.value c w).1 * 2 ^ (c.n + 1)).den = 1 ∧
      ((admittedValue B1 B2 Builder.value c w).2 * 2 ^ (c.n + 1)).den = 1 :=
  ⟨(admittedValue_scaled B1 B2 c w).1.den, (admittedValue_scaled B1 B2 c w).2.den⟩

theorem admittedValue_dyadic (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    IsDyadic (admittedValue B1 B2 Builder.value c w).1 ∧ IsDyadic (admittedValue B1 B2 Builder.value c w).2 :=
  ⟨⟨c.n + 1, (admittedValue_den B1 B2 c w).1⟩, ⟨c.n + 1, (admittedValue_den B1 B2 c w).2⟩⟩

/-- `prop:time`: output words of `O(n)` bits, `|outputWord (p̂, κ̂)| ≤ 8n + 50`. -/
theorem admittedValue_outputWord_length (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    (outputWord (admittedValue B1 B2 Builder.value c w)).length ≤ 8 * c.n + 50 := by
  have h1 := (admittedValue_scaled B1 B2 c w).1.ratWord_length
  have h2 := (admittedValue_scaled B1 B2 c w).2.ratWord_length
  simp only [outputWord, List.length_append]
  omega

/-! ## Normalized calls -/

/-- With unit top coefficients, the top weight of a circuit is its number of occurrences, at most its wire count
(`def:class`). -/
theorem topWeight_le_wires {n B : ℕ} {C : NCircuit n} (hw : C.WellFormed B) (hu : Transfer.UnitTop C) :
    C.topWeight ≤ Transfer.wires C := by
  have h1 : (C.coeffs.map Int.natAbs).sum = C.coeffs.length := by
    have : C.coeffs.map Int.natAbs = List.replicate C.coeffs.length 1 :=
      List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
        rw [hu a ha]; rfl⟩
    rw [this, List.sum_replicate, smul_eq_mul, mul_one]
  have h2 : ∀ gs : List (NormalizedThresholdGate n), gs.length ≤ (gs.map fun g => Transfer.fanIn g + 1).sum := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  unfold NCircuit.topWeight
  rw [h1, ← hw.1]
  exact h2 C.gates

/-- A normalized call of §3.1 (`Transfer.Admitted4`) is a normalized call in the sense of `Call.Admitted`: its total
top weight is at most its wire count `W ≤ 2n⁴`. -/
theorem admitted_of_admitted4 {B1 B2 : ℕ} {c : Call} (h : Transfer.Admitted4 B1 B2 c) : c.Admitted B1 B2 := by
  obtain ⟨h4, hf, hs, hu1, hu2, hpair, hpar, hpari, hW, hr1, hr2, hr3, hpl⟩ := h
  refine ⟨h4, hf, hs, hpair, hpar, hpari, ?_, hr1, hr2, hr3, hpl⟩
  have e1 := topWeight_le_wires hf hu1
  have e2 := topWeight_le_wires hs hu2
  unfold Call.W
  unfold Transfer.callWires at hW
  omega

/-- The call word of a normalized call has polynomial length (`thm:counter`). -/
theorem callWord_length_le {B1 B2 : ℕ} {c : Call} (h : Transfer.Admitted4 B1 B2 c) :
    (callWord c).length ≤ NearCubicGates.Close.CounterAsm.callBound B2 c.n :=
  NearCubicGates.Close.CounterAsm.callWord_le c (admitted_of_admitted4 h)

end NearQuarticWires.Program
