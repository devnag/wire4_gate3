import Proof.Quartic.Builder.Filter
import Proof.Quartic.Builder.CounterMath
import Proof.Foundations.SupplierPrinter

/-!
# The witness law of the proof of `prop:complete`

Paper: the witness, paper/paper.tex; the proof of `prop:complete`.

`witnessWord idx 𝒮 ξ` writes a witness in the order of `Algorithm.decodeWitness`: the `k` bits of the partition
index (lowest first), one bit per occurrence label for `𝒮`, and the `J` vectors `ξ_r` over all occurrence labels.
The decoding lemmas read back the partition (`translation_witnessWord`) and the selection
(`selection_witnessWord`).

`witnessLaw`: the partition index of `lem:meanpop`, the selection `𝒮` with the law of `lem:filter`
(`selectionWeight`), and the vectors `ξ` with any law `Q`, independent of `𝒮`. For it the paragraph bounds of
`prop:complete` reduce to one bound, the expected fraction of columns where the conclusion of `lem:localize` fails
(`LocalizationBound`); the other four event bounds are proved (`structuralMass_le`, `populationMass_le`,
`filterMass_le`, `wideMass_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset MeasureTheory
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

theorem getD_ofFn_append_lt {m : ℕ} (f : Fin m → Bool) (rest : List Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn f ++ rest).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_ofFn]

theorem getD_ofFn_append_add {m : ℕ} (f : Fin m → Bool) (rest : List Bool) (i : ℕ) :
    (List.ofFn f ++ rest).getD (m + i) false = rest.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem pos_of_lt_mul {m a b : ℕ} (h : m < a * b) : 0 < b := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rw [hb, Nat.mul_zero] at h
    omega
  · exact hb

theorem lt_mul_comm {m a b : ℕ} (h : m < a * b) : m < b * a := by
  rw [Nat.mul_comm]
  exact h

section Word

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

/-- The witness word (`sec:algorithm`, paper/paper.tex) of a partition index, a selection `𝒮` and vectors `ξ`,
in the order read by `Algorithm.decodeWitness`. -/
def witnessWord (idx : Fin (2 ^ p.k)) (s : Fin (allGates c).length → Bool)
    (ξ : Fin p.J → Fin (allGates c).length → Bool) : List Bool :=
  List.ofFn (fun i : Fin p.k => (idx : ℕ).testBit i) ++
    (List.ofFn s ++ List.ofFn fun q : Fin (p.J * (allGates c).length) =>
      ξ ⟨q / (allGates c).length, Nat.div_lt_of_lt_mul (lt_mul_comm q.isLt)⟩
        ⟨q % (allGates c).length, Nat.mod_lt _ (pos_of_lt_mul q.isLt)⟩)

theorem witnessWord_length (idx : Fin (2 ^ p.k)) (s : Fin (allGates c).length → Bool)
    (ξ : Fin p.J → Fin (allGates c).length → Bool) :
    (witnessWord c idx s ξ).length = p.k + (allGates c).length + p.J * (allGates c).length := by
  unfold witnessWord
  simp only [List.length_append, List.length_ofFn]
  ring

/-- (W2) read back: the selection of the word is `𝒮`. -/
theorem selection_witnessWord (idx : Fin (2 ^ p.k)) (s : Fin (allGates c).length → Bool)
    (ξ : Fin p.J → Fin (allGates c).length → Bool) :
    selection c (p := p) (witnessWord c idx s ξ) = s := by
  funext i
  unfold selection Algorithm.witnessBit witnessWord
  rw [getD_ofFn_append_add, getD_ofFn_append_lt _ _ _ i.isLt]

/-- (W3) read back: the bit `ξ^{(j)}_{i+1,t}` of the word is `ξ_i` at the label of occurrence `t` of circuit `j`
(`allGates` lists the occurrences of `C¹` before those of `C²`). -/
theorem chainBit_witnessWord (idx : Fin (2 ^ p.k)) (s : Fin (allGates c).length → Bool)
    (ξ : Fin p.J → Fin (allGates c).length → Bool) (j : Fin 2) (i : Fin p.J) (t : Fin (occurrences c j)) :
    chainBit c (p := p) (witnessWord c idx s ξ) j i t =
      Algorithm.CellCall.bitInt (ξ i ⟨(if j = 0 then 0 else c.first.gates.length) + t, by
        have ht := t.isLt
        fin_cases j
        all_goals simp [occurrences, gatesOf, allGates] at ht ⊢
        all_goals omega⟩) := by
  have hG : (allGates c).length = c.first.gates.length + c.second.gates.length := by simp [allGates]
  have hoff : (if j = 0 then 0 else c.first.gates.length) + (t : ℕ) < (allGates c).length := by
    have ht := t.isLt
    fin_cases j
    all_goals simp [occurrences, gatesOf, allGates] at ht ⊢
    all_goals omega
  unfold chainBit
  rw [dif_pos i.isLt]
  congr 1
  change Algorithm.witnessBit (witnessWord c idx s ξ)
    (p.k + (occurrences c 0 + occurrences c 1) + (i : ℕ) * (occurrences c 0 + occurrences c 1) +
      (if j = 0 then 0 else occurrences c 0) + t) = _
  have h01 : occurrences c 0 + occurrences c 1 = (allGates c).length := by
    simp [occurrences, gatesOf, allGates]
  have h0 : occurrences c 0 = c.first.gates.length := rfl
  rw [h01, h0]
  unfold Algorithm.witnessBit witnessWord
  rw [show p.k + (allGates c).length + (i : ℕ) * (allGates c).length +
      (if j = 0 then 0 else c.first.gates.length) + (t : ℕ) =
      p.k + ((allGates c).length + ((i : ℕ) * (allGates c).length +
        ((if j = 0 then 0 else c.first.gates.length) + (t : ℕ)))) by ring]
  rw [getD_ofFn_append_add, getD_ofFn_append_add]
  have hq : (i : ℕ) * (allGates c).length + ((if j = 0 then 0 else c.first.gates.length) + (t : ℕ)) <
      p.J * (allGates c).length := by
    have := i.isLt
    nlinarith
  rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_ofFn]
  congr 1
  · apply Fin.ext
    simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hoff, Nat.zero_add]
  · apply Fin.ext
    simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]

/-- (W1) read back: the partition index of the word is `idx`. -/
theorem partitionIndex_witnessWord (idx : Fin (2 ^ p.k)) (s : Fin (allGates c).length → Bool)
    (ξ : Fin p.J → Fin (allGates c).length → Bool) :
    (witness c (p := p) (witnessWord c idx s ξ)).partitionIndex = idx := by
  apply Fin.ext
  change (∑ i ∈ Finset.range p.k, if Algorithm.witnessBit (witnessWord c idx s ξ) i then 2 ^ i else 0) % 2 ^ p.k =
    (idx : ℕ)
  have hbits : ∀ i ∈ Finset.range p.k, (if Algorithm.witnessBit (witnessWord c idx s ξ) i then 2 ^ i else 0) =
      if (idx : ℕ).testBit i then 2 ^ i else 0 := by
    intro i hi
    unfold Algorithm.witnessBit witnessWord
    rw [getD_ofFn_append_lt _ _ _ (Finset.mem_range.mp hi)]
  rw [Finset.sum_congr rfl hbits, Finset.sum_range (fun i => if (idx : ℕ).testBit i then 2 ^ i else 0),
    NearCubicWires.SupplierPrinter.testBit_sum_eq idx.isLt, Nat.mod_eq_of_lt idx.isLt]

/-- (W1) read back: the partition named by the word. -/
theorem translation_witnessWord (idx : Fin (2 ^ p.k)) (s : Fin (allGates c).length → Bool)
    (ξ : Fin p.J → Fin (allGates c).length → Bool) :
    translation c hs (witnessWord c idx s ξ) = translationEquiv c hs idx := by
  unfold translation
  rw [partitionIndex_witnessWord]

/-- The partition index of `lem:meanpop`. -/
noncomputable def goodIndex : Fin (2 ^ p.k) := (translationEquiv c hs).symm (goodTranslation c hs)

theorem translation_goodIndex (s : Fin (allGates c).length → Bool) (ξ : Fin p.J → Fin (allGates c).length → Bool) :
    translation c hs (witnessWord c (goodIndex c hs) s ξ) = goodTranslation c hs := by
  rw [translation_witnessWord, goodIndex, Equiv.apply_symm_apply]

include hs in
/-- The witness length: `k + G + J G ≤ n + (n + 2) · 2n⁴`, with `G ≤ W ≤ 2n⁴` and `J ≤ μ_n + 1 ≤ n + 1`. -/
theorem witnessWord_length_le (idx : Fin (2 ^ p.k)) (s : Fin (allGates c).length → Bool)
    (ξ : Fin p.J → Fin (allGates c).length → Bool) :
    (witnessWord c idx s ξ).length ≤ witnessLength c.n := by
  rw [witnessWord_length]
  have hk : p.k ≤ c.n := (Cells.ParameterRules.k_lt_n hs).le
  have hv := hs.input_valid
  have hG : (allGates c).length ≤ 2 * c.n ^ 4 := by
    have h1 : (allGates c).length = (callInput c).G1 + (callInput c).G2 := by
      simp [allGates, callInput]
    rw [h1]
    exact hv.2.2.1.trans hv.2.2.2.1
  have hJ : p.J ≤ c.n + 1 := by
    have h1 := hs.J_bound
    rw [hs.Jmax_eq] at h1
    have h2 : p.mu ≤ p.lambda := Cells.ParameterRules.mu_le_lambda hs
    have h3 : p.lambda ≤ c.n := by
      rw [hs.lambda_eq]
      exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    omega
  unfold witnessLength
  have : (1 + p.J) * (allGates c).length ≤ (c.n + 2) * (2 * c.n ^ 4) :=
    Nat.mul_le_mul (by omega) hG
  nlinarith

end Word

/-! ### The law -/

section Law

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (callInput c) p)

theorem selectionWeight_nonneg (s : Fin (allGates c).length → Bool) : 0 ≤ selectionWeight c hs s :=
  measureReal_nonneg

theorem sum_selectionWeight : ∑ s, selectionWeight c hs s = 1 := by
  unfold selectionWeight
  rw [sum_measureReal_singleton]
  simp

/-- **`lem:filter`(b) and `lem:localize` for the witness law** (paper/paper.tex): there is a law
`Q` of the vectors `ξ` such that, for the partition of `lem:meanpop` and `𝒮` independent of `ξ` with the law of
`lem:filter`, the expected fraction of columns where the conclusion of `lem:localize` fails on some walk of mask one
is at most `β/16 + β/8`. -/
def LocalizationBound : Prop :=
  ∃ Q : (Fin p.J → Fin (allGates c).length → Bool) → ℝ, (∀ ξ, 0 ≤ Q ξ) ∧ ∑ ξ, Q ξ = 1 ∧
    ∑ s, ∑ ξ, selectionWeight c hs s * Q ξ *
      unlocalizedFraction c hs (witnessWord c (goodIndex c hs) s ξ) ≤ 3 * (c.radius : ℝ) / 16

/-- **The random bounds of `prop:complete` from the localization bound** (paper/paper.tex): the
product law of the partition of `lem:meanpop`, `𝒮` and `ξ` satisfies `lem:filter`(a) and (c) on its own
(`filterMass_le`, `wideMass_le`). -/
noncomputable def randomBounds_of_localization (hcond : CompletenessConditions c p)
    (Q : (Fin p.J → Fin (allGates c).length → Bool) → ℝ) (hQ0 : ∀ ξ, 0 ≤ Q ξ) (hQ1 : ∑ ξ, Q ξ = 1)
    (hloc : ∑ s, ∑ ξ, selectionWeight c hs s * Q ξ *
      unlocalizedFraction c hs (witnessWord c (goodIndex c hs) s ξ) ≤ 3 * (c.radius : ℝ) / 16) :
    RandomBounds c hs (witnessLength c.n) := by
  classical
  let Ω := (Fin (allGates c).length → Bool) × (Fin p.J → Fin (allGates c).length → Bool)
  let word : Ω → List Bool := fun ω => witnessWord c (goodIndex c hs) ω.1 ω.2
  let P : Ω → ℝ := fun ω => selectionWeight c hs ω.1 * Q ω.2
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => mul_nonneg (selectionWeight_nonneg c hs _) (hQ0 _)
  have hsel : ∀ ω : Ω, selection c (p := p) (word ω) = ω.1 := fun ω => selection_witnessWord c _ _ _
  have hpart : ∀ ω : Ω, translation c hs (word ω) = goodTranslation c hs := fun ω => translation_goodIndex c hs _ _
  have hmarg : ∀ s, ∑ ω : Ω, P ω * ind (ω.1 = s) = selectionWeight c hs s := by
    intro s
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single s]
    · show ∑ x, selectionWeight c hs s * Q x * ind ((s, x).1 = s) = selectionWeight c hs s
      rw [Finset.sum_congr rfl (fun x _ => by rw [ind_of ((s, x).1 = s) rfl, mul_one]), ← Finset.mul_sum, hQ1,
        mul_one]
    · intro s' _ hs'
      refine Finset.sum_eq_zero fun ξ _ => ?_
      have : ind ((s', ξ).1 = s) = 0 := by unfold ind; rw [if_neg hs']
      rw [this, mul_zero]
    · simp
  exact
    { Ω := Ω
      word := word
      length_le := fun ω => witnessWord_length_le c hs _ _ _
      partition := hpart
      P := P
      nonneg := hP0
      total := by
        rw [Fintype.sum_prod_type]
        simp only [P, ← Finset.mul_sum, hQ1, mul_one]
        exact sum_selectionWeight c hs
      filter := filterMass_le c hs P word Prod.fst hsel (goodTranslation c hs) hpart hmarg hcond.k_large
      wide := wideMass_le c hs P hP0 word Prod.fst hsel (goodTranslation c hs) hpart hmarg hcond.Xmax_large
      unlocalized := by
        rw [Fintype.sum_prod_type]
        exact hloc }

end Law

/-- **`thm:counter`(i),(ii) for `Builder.value`, with every part of `prop:complete` proved except `lem:localize`**:
the hypotheses are the cap of `lem:asymptotics` and, for every call meeting the hypotheses of `prop:complete`, the
localization bound (`lem:filter`(b) and `lem:localize` for some law of the vectors `ξ`). -/
noncomputable def counterMath4_of_localization {B1 B2 : ℕ} (hcap : QuarticCap B1 B2)
    (hloc : ∀ (c : Call) (p : Cells.Parameters) (hs : Cells.ParameterRules (callInput c) p), Shaped c →
      CompletenessConditions c p → LocalizationBound c hs) :
    CounterMath4 B1 B2 :=
  counterMath4_of_random hcap fun c p hs hc hcond => by
    obtain ⟨Q, hQ0, hQ1, h⟩ := hloc c p hs hc hcond
    exact ⟨randomBounds_of_localization c hs hcond Q hQ0 hQ1 h⟩

end NearQuarticWires.Builder
