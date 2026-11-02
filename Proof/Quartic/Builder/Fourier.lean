import Proof.Quartic.Builder.Facts
import Proof.Quartic.Sampler.CellParity

/-!
# `lem:fourier` for the constructed cell call

Paper: `lem:fourier`, paper/paper.tex, and the matrices `M_θ(z)` with the mask inside.

For a call with unit top coefficients, the predicate at a point of a cell is a lookup of the two scores
(`pred_eq_lookup`), and for a parity call the lookup of the first score exclusive-or the input parity
(`pred_eq_parity`). The Fourier rows are then the decompositions imported from `Proof.Quartic.Sampler`:
* single and pair calls: `Sampler.cell_fourier_decomposition`, with index set `Θ`, coefficients `F̂(θ, 0)` and
  selectors `a = ω^{θ s^L}`, `b = ω^{θ s^R}`;
* parity calls: `Sampler.parity_masked_score_decomposition`, with index set `Θ × {0,1}`, coefficients
  `Sampler.parityCoefficient` and selectors carrying the parity characters `χ_0 χ_L`, `χ_R`.

In both cases the total coefficient mass is at most `M_F = ⌈√|Θ|⌉` (`Sampler.coefficient_mass_le_integer`,
`Sampler.parityCoefficient_mass_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-! ### Circuits with unit top coefficients -/

/-- With unit top coefficients, the score of a circuit is its number of accepting occurrences. -/
theorem zip_unit_sum {n : ℕ} (z : BitInput n) (gs : List (NormalizedThresholdGate n)) (cs : List ℤ)
    (hl : gs.length = cs.length) (h1 : ∀ a ∈ cs, a = 1) :
    ((gs.zip cs).map fun gc => gc.2 * if gc.1.eval z then 1 else 0).sum = (gs.map fun g => bitZ (g.eval z)).sum := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    cases cs with
    | nil => simp at hl
    | cons a cs =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      have ha : a = 1 := h1 a (by simp)
      rw [ih cs (by simpa using hl) (fun b hb => h1 b (by simp [hb])), ha]
      simp [bitZ]

/-- With unit top coefficients, the top weight of a circuit is its number of coefficients. -/
theorem natAbs_unit_sum (cs : List ℤ) (h1 : ∀ a ∈ cs, a = 1) : (cs.map Int.natAbs).sum = cs.length := by
  induction cs with
  | nil => simp
  | cons a cs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h1 a (by simp), ih (fun b hb => h1 b (by simp [hb]))]
    simp [Nat.add_comm]

/-- A `SYM∘THR` circuit with unit top coefficients and one coefficient per occurrence evaluates to its table at
index `G + (number of accepting occurrences)` (`def:class`, the table on `[0, G]` stored at indices `G … 2G`). -/
theorem eval_unit {n : ℕ} (C : NCircuit n) (h1 : Transfer.UnitTop C) (hl : C.gates.length = C.coeffs.length)
    (z : BitInput n) :
    C.eval z = C.table.getD (((C.gates.map fun g => bitZ (g.eval z)).sum : ℤ).toNat + C.gates.length) false := by
  have hs : C.score z = (C.gates.map fun g => bitZ (g.eval z)).sum := zip_unit_sum z C.gates C.coeffs hl h1
  have ht : C.topWeight = C.gates.length := by
    unfold NCircuit.topWeight
    rw [natAbs_unit_sum C.coeffs h1, hl]
  have hnn : 0 ≤ (C.gates.map fun g => bitZ (g.eval z)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    unfold bitZ
    split_ifs <;> norm_num
  unfold NCircuit.eval
  rw [hs, ht]
  congr 1
  omega

/-! ### The predicate on a cell -/

/-- The lookup `g(s_1, s_2) = g_1(s_1) ⊕ g_2(s_2)` of a single or pair call on its two scores (`lem:fourier`); for a single call the second circuit is empty and contributes `false`. -/
def lookup (c : Call) (s : ℕ × ℕ) : Bool :=
  xor (c.first.table.getD (s.1 + c.first.gates.length) false)
    (c.second.table.getD (s.2 + c.second.gates.length) false)

/-- The lookup `g_1(s_1)` of the first circuit of a parity call (`lem:fourier`). -/
def lookupFirst (c : Call) (s : ℕ × ℕ) : Bool := c.first.table.getD (s.1 + c.first.gates.length) false

/-- The table `[false]` of the empty circuit reads `false` everywhere. -/
theorem getD_single_false (i : ℕ) : ([false] : List Bool).getD i false = false := by
  cases i <;> simp

section Cell

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p) (w : List Bool)

/-- A circuit with unit tops evaluates, at a point of a cell, to its table at its score. -/
theorem eval_point (C : NCircuit c.n) (h1 : Transfer.UnitTop C) (hl : C.gates.length = C.coeffs.length)
    (x : BitInput c.n) (u v : (star c hs).Errors) :
    C.eval ((star c hs).point x u v) =
      C.table.getD ((Cells.score (star c hs) C.gates x u v).toNat + C.gates.length) false :=
  eval_unit C h1 hl _

/-- `lem:identity` for single and pair calls: `pred(c(z) ⊕ u ⊕ v) = g(s_1, s_2)`. -/
theorem pred_eq_lookup (hc : Shaped c) (hk : c.kind ≠ .parity) (z : Fin (cellCall c hs w).ncol)
    (u v : Fin (cellCall c hs w).seed.N) :
    (cellCall c hs w).pred z (u, v) = lookup c
      ((Cells.score (star c hs) c.first.gates (center c hs w z) (pattern c hs u) (pattern c hs v)).toNat,
       (Cells.score (star c hs) c.second.gates (center c hs w z) (pattern c hs u) (pattern c hs v)).toNat) := by
  change c.predicate _ = _
  unfold Call.predicate lookup
  have e1 := eval_point c hs c.first hc.first_unit hc.first_length (center c hs w z) (pattern c hs u)
    (pattern c hs v)
  have e2 := eval_point c hs c.second hc.second_unit hc.second_length (center c hs w z) (pattern c hs u)
    (pattern c hs v)
  cases hkind : c.kind with
  | single =>
    have hsec := hc.second_empty (by rw [hkind]; exact nofun)
    simp only
    rw [e1]
    have : c.second.table = [false] := by rw [hsec]; rfl
    rw [this]
    rw [getD_single_false]
    simp
  | pair =>
    simp only
    rw [e1, e2]
  | parity => exact absurd hkind hk

/-- `lem:identity` for parity calls: `pred(c(z) ⊕ u ⊕ v) = g_1(s_1) ⊕ PAR_Σ(c(z) ⊕ u ⊕ v)`. -/
theorem pred_eq_parity (hc : Shaped c) (hk : c.kind = .parity) (z : Fin (cellCall c hs w).ncol)
    (u v : Fin (cellCall c hs w).seed.N) :
    (cellCall c hs w).pred z (u, v) = xor (lookupFirst c
      ((Cells.score (star c hs) c.first.gates (center c hs w z) (pattern c hs u) (pattern c hs v)).toNat,
       (Cells.score (star c hs) c.second.gates (center c hs w z) (pattern c hs u) (pattern c hs v)).toNat))
      (c.parityOf ((star c hs).point (center c hs w z) (pattern c hs u) (pattern c hs v))) := by
  change c.predicate _ = _
  unfold Call.predicate lookupFirst
  rw [hk]
  simp only
  rw [eval_point c hs c.first hc.first_unit hc.first_length]

/-- `lem:fourier`, paper/paper.tex: the sign `(-1)^{PAR_Σ}` of the call's parity is multiplicative
over the exclusive-or of inputs (indices outside `[n]` read `0`, repeated indices cancel). -/
theorem bitSign_parityOf_xor (x y : BitInput c.n) :
    Sampler.bitSign (c.parityOf (xorInput x y)) =
      Sampler.bitSign (c.parityOf x) * Sampler.bitSign (c.parityOf y) := by
  unfold Call.parityOf
  simp only [List.foldl_map]
  rw [Sampler.bitSign_foldl, Sampler.bitSign_foldl, Sampler.bitSign_foldl]
  simp only [Sampler.bitSign, Bool.false_eq_true, if_false, one_mul]
  rw [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases h : i < c.n
  · simp only [h, dif_pos, xorInput]
    cases x ⟨i, h⟩ <;> cases y ⟨i, h⟩ <;> norm_num
  · simp [h]

/-- The parity sign at a point of a cell is the column sign times a left and a right selector. -/
theorem bitSign_parityOf_point (x : BitInput c.n) (u v : (star c hs).Errors) :
    Sampler.bitSign (c.parityOf ((star c hs).point x u v)) =
      (Sampler.bitSign (c.parityOf x) *
        Sampler.bitSign (c.parityOf ((star c hs).errorVector (star c hs).leftBlock u))) *
        Sampler.bitSign (c.parityOf ((star c hs).errorVector (star c hs).rightBlock v)) := by
  have h1 := bitSign_parityOf_xor c (xorInput x ((star c hs).errorVector (star c hs).leftBlock u))
    ((star c hs).errorVector (star c hs).rightBlock v)
  have h2 := bitSign_parityOf_xor c x ((star c hs).errorVector (star c hs).leftBlock u)
  rw [h2] at h1
  exact h1

theorem norm_bitSign_le (b : Bool) : ‖Sampler.bitSign b‖ ≤ 1 := by
  cases b <;> simp [Sampler.bitSign]

/-- `sec:params` item 4: `|Θ| = Ω_1 Ω_2 ≤ M_F²`. -/
theorem omega_le_MF_sq (hs : Cells.ParameterRules (callInput c) p) :
    Sampler.omega 4 c.first.gates.length * Sampler.omega 4 c.second.gates.length ≤ p.MF ^ 2 := by
  rw [hs.MF_eq, hs.omega1_eq, hs.omega2_eq, hs.m_eq]
  exact Cells.ParameterArithmetic.le_ceilSqrt_sq _

/-- `lem:fourier`, paper/paper.tex: `[a ⊕ b] = ½ - ½ (-1)^a (-1)^b`. -/
theorem boolBit_xor (a b : Bool) :
    Sampler.boolBit (xor a b) = (1 / 2 : ℂ) - (1 / 2 : ℂ) * Sampler.bitSign a * Sampler.bitSign b := by
  cases a <;> cases b <;> norm_num [Sampler.boolBit, Sampler.bitSign]

/-- A bit times an integer mask value, as a complex number. -/
theorem cast_bit_mul (b : Bool) (m : ℤ) :
    ((((Algorithm.CellCall.bitInt b * m : ℤ) : ℝ)) : ℂ) = Sampler.boolBit b * (((m : ℤ) : ℝ) : ℂ) := by
  cases b <;> simp [Algorithm.CellCall.bitInt, Sampler.boolBit]

/-- **`lem:fourier` for single and pair calls** (paper/paper.tex): coefficients
`F̂(θ) = |Θ|^{-1} Σ_t F(t) ω^{-θ t}` of the lookup, of total mass at most `M_F`, with the unimodular selectors
`a_{z,θ}(u) = ω^{θ s^L(z,u)}` and `b_{z,θ}(v) = ω^{θ s^R(z,v)}`. -/
noncomputable def scoreRows (hc : Shaped c) (hk : c.kind ≠ .parity) : (cellCall c hs w).FourierRows where
  Index := Sampler.Frequency 4 c.first.gates.length c.second.gates.length
  frequency := id
  coefficient := Sampler.coefficient (Sampler.lookupExtension 4 c.first.gates.length c.second.gates.length
    (lookup c))
  mass := by
    have h := Sampler.coefficient_mass_le_integer
      (Sampler.lookupExtension 4 c.first.gates.length c.second.gates.length (lookup c))
      (Sampler.norm_lookupExtension_le 4 _ _ _) p.MF (omega_le_MF_sq c hs)
    exact h
  left z θ u := Sampler.phase θ
    (Cells.scoreLeft (star c hs) c.first.gates (center c hs w z) (pattern c hs u))
    (Cells.scoreLeft (star c hs) c.second.gates (center c hs w z) (pattern c hs u))
  right z θ v := Sampler.phase θ
    (Cells.scoreRight (star c hs) c.first.gates (center c hs w z) (pattern c hs v))
    (Cells.scoreRight (star c hs) c.second.gates (center c hs w z) (pattern c hs v))
  left_le z θ u := by rw [Sampler.norm_phase]
  right_le z θ v := by rw [Sampler.norm_phase]
  row z u v := by
    have hd := Sampler.cell_fourier_decomposition (N := hs.seedParameters.N) (star c hs) 4 (by norm_num)
      c.first.gates c.second.gates (lookup c) (center c hs w z) (pattern c hs)
      ((cellCall c hs w).realMask z) u v
    refine Eq.trans ?_ hd
    unfold Algorithm.CellCall.maskedAccept
    rw [cast_bit_mul, pred_eq_lookup c hs w hc hk z u v]
    rfl

/-- **`lem:fourier` for parity calls** (paper/paper.tex): `pred = ½ - ½ χ_0 χ_L(u) χ_R(v) Γ_g(s_1)`,
with coefficients `F̂(0,0) = ½`, `F̂(θ,1) = -½ Γ̂_g(θ)` and selectors `χ_0 χ_L ω^{θ s^L}`, `χ_R ω^{θ s^R}`. -/
noncomputable def parityRows (hc : Shaped c) (hk : c.kind = .parity) : (cellCall c hs w).FourierRows where
  Index := Sampler.Frequency 4 c.first.gates.length c.second.gates.length × Fin 2
  frequency := Prod.fst
  coefficient := Sampler.parityCoefficient
    (Sampler.signLookupExtension 4 c.first.gates.length c.second.gates.length (lookupFirst c))
  mass := by
    have h := Sampler.parityCoefficient_mass_le
      (Sampler.signLookupExtension 4 c.first.gates.length c.second.gates.length (lookupFirst c))
      (Sampler.norm_signLookupExtension_le 4 _ _ _) p.MF (omega_le_MF_sq c hs)
    exact h
  left z := Sampler.paritySelector
    (fun u => Sampler.bitSign (c.parityOf (center c hs w z)) *
      Sampler.bitSign (c.parityOf ((star c hs).errorVector (star c hs).leftBlock (pattern c hs u))))
    (fun u => Cells.scoreLeft (star c hs) c.first.gates (center c hs w z) (pattern c hs u))
    (fun u => Cells.scoreLeft (star c hs) c.second.gates (center c hs w z) (pattern c hs u))
  right z := Sampler.paritySelector
    (fun v => Sampler.bitSign (c.parityOf ((star c hs).errorVector (star c hs).rightBlock (pattern c hs v))))
    (fun v => Cells.scoreRight (star c hs) c.first.gates (center c hs w z) (pattern c hs v))
    (fun v => Cells.scoreRight (star c hs) c.second.gates (center c hs w z) (pattern c hs v))
  left_le z t u := Sampler.paritySelector_norm _
    (fun u => by rw [norm_mul]; exact mul_le_one₀ (norm_bitSign_le _) (norm_nonneg _) (norm_bitSign_le _)) _ _ t u
  right_le z t v := Sampler.paritySelector_norm _ (fun v => norm_bitSign_le _) _ _ t v
  row z u v := by
    have hd := Sampler.parity_masked_score_decomposition (N := hs.seedParameters.N) (m := 4)
      (Sampler.signLookupExtension 4 c.first.gates.length c.second.gates.length (lookupFirst c))
      (fun u => Sampler.bitSign (c.parityOf (center c hs w z)) *
        Sampler.bitSign (c.parityOf ((star c hs).errorVector (star c hs).leftBlock (pattern c hs u))))
      (fun v => Sampler.bitSign (c.parityOf ((star c hs).errorVector (star c hs).rightBlock (pattern c hs v))))
      (fun u => Cells.scoreLeft (star c hs) c.first.gates (center c hs w z) (pattern c hs u))
      (fun u => Cells.scoreLeft (star c hs) c.second.gates (center c hs w z) (pattern c hs u))
      (fun v => Cells.scoreRight (star c hs) c.first.gates (center c hs w z) (pattern c hs v))
      (fun v => Cells.scoreRight (star c hs) c.second.gates (center c hs w z) (pattern c hs v))
      (fun q => Cells.residual (star c hs) c.first.gates (center c hs w z) (pattern c hs q.1) (pattern c hs q.2))
      (fun q => Cells.residual (star c hs) c.second.gates (center c hs w z) (pattern c hs q.1) (pattern c hs q.2))
      ((cellCall c hs w).realMask z) u v
    have hF : ∀ a b : (star c hs).Errors,
        Sampler.signLookupExtension 4 c.first.gates.length c.second.gates.length (lookupFirst c)
          (((Cells.scoreLeft (star c hs) c.first.gates (center c hs w z) a + Cells.scoreRight (star c hs) c.first.gates (center c hs w z) b +
              Cells.residual (star c hs) c.first.gates (center c hs w z) a b : ℤ) : ZMod (Sampler.omega 4 c.first.gates.length)),
            ((Cells.scoreLeft (star c hs) c.second.gates (center c hs w z) a + Cells.scoreRight (star c hs) c.second.gates (center c hs w z) b +
              Cells.residual (star c hs) c.second.gates (center c hs w z) a b : ℤ) : ZMod (Sampler.omega 4 c.second.gates.length))) =
        Sampler.bitSign (lookupFirst c ((Cells.score (star c hs) c.first.gates (center c hs w z) a b).toNat,
          (Cells.score (star c hs) c.second.gates (center c hs w z) a b).toNat)) := by
      intro a b
      rw [← Cells.score_identity, ← Cells.score_identity]
      exact Sampler.signLookupExtension_cast (by norm_num) (lookupFirst c) _ _
        (Cells.score_bounds (star c hs) c.first.gates (center c hs w z) a b) (Cells.score_bounds (star c hs) c.second.gates (center c hs w z) a b)
    dsimp only at hd
    rw [hF] at hd
    refine Eq.trans ?_ hd
    have hp := bitSign_parityOf_point c hs (center c hs w z) (pattern c hs u) (pattern c hs v)
    have hpred := pred_eq_parity c hs w hc hk z u v
    unfold Algorithm.CellCall.maskedAccept
    rw [cast_bit_mul, hpred, boolBit_xor, hp]
    unfold Algorithm.CellCall.realMask
    ring_nf
    rfl

/-- **`lem:fourier`** for the cell call of any shaped call: the parity form for parity calls and the score form
otherwise. -/
noncomputable def fourierRows (hc : Shaped c) : (cellCall c hs w).FourierRows :=
  if hk : c.kind = .parity then parityRows c hs w hc hk else scoreRows c hs w hc hk

end Cell

end NearQuarticWires.Builder
