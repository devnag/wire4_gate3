import Proof.Quartic.Algorithm.Reconstruction
import Proof.Quartic.Cycle.ConditionalBounds
import Proof.Quartic.Cycle.EmptyPrefix
import Proof.Quartic.Sampler.ErrorBounds

/-!
# Soundness of the counting algorithm (`prop:sound`)

Paper: `prop:sound`, paper/paper.tex. For every witness, the interval returned by the algorithm
contains `p_true = Pr_x[pred(x) = 1]`.

The proof follows the paper's four steps.
* **(1) Exact conditional potentials**: the printed sums are a fixed positive multiple of the
  conditional potentials, `Ψ̃(π) = 2^S (4^m / 2|Θ|) Ψ(π)` with `Ψ(π) = Σ_{z ∈ Z_c} E[Φ_z | π]`. This is the
  hypothesis `PotentialsExact` of `sound_of_exact_potentials`.
* **(2) Greedy choice**: by `imp:seed` the two children of a prefix average to the parent
  (`Cycle.conditionalPotential_children`), so the potential of the chosen seed is at most that of the empty prefix,
  which is the independent-sample mean (`Cycle.conditionalPotential_empty`), bounded by `lem:tracebound`
  (`Sampler.mean_sum_columnPotential_le`).
* **(3) Sampler error**: `lem:root` turns the potential bound into an average error at most `η`
  (`Sampler.average_mask_error`, `Sampler.average_masked_predicate_error`, which also apply `lem:selector` and
  `lem:fourier`).
* **(4) Per-column intervals**: `V_m ≤ V ≤ V_m + 1 - μ` at every column, and summing gives
  `Lo ≤ p_true ≤ Hi`; outward rounding preserves this.
-/

set_option autoImplicit false

namespace NearQuarticWires.Algorithm

open Finset
open NearQuarticWires.Sampler (Cell Frequency omega)
open NearCubicWires.WireExponent3_5.Shared (uMean)

/-! ### (2) The greedy choice never increases a potential whose children average to it -/

/-- `prop:sound` step (2), paper/paper.tex: if the objective `Ψ̃` is a positive multiple `c Ψ` of a
potential `Ψ` on all prefixes of length at most `S`, and the two children of every shorter prefix average to it,
then after `i ≤ S` greedy rounds the prefix has length `i` and potential at most `Ψ([])`. -/
theorem greedy_descent (S : ℕ) (Ψt : List Bool → ℚ) (Ψ : List Bool → ℝ) (c : ℝ) (hc : 0 < c)
    (hexact : ∀ π : List Bool, π.length ≤ S → (Ψt π : ℝ) = c * Ψ π)
    (hchild : ∀ π : List Bool, π.length < S →
      Ψ π = (Ψ (π ++ [true]) + Ψ (π ++ [false])) / 2) :
    ∀ i ≤ S, ((greedyStep Ψt)^[i] []).length = i ∧ Ψ ((greedyStep Ψt)^[i] []) ≤ Ψ [] := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    obtain ⟨hlen, hle⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    set π := (greedyStep Ψt)^[i] [] with hπdef
    have hπ : π.length < S := by omega
    have hc1 := hexact (π ++ [true]) (by simp; omega)
    have hc0 := hexact (π ++ [false]) (by simp; omega)
    have havg := hchild π hπ
    refine ⟨by simp [greedyStep, hlen], ?_⟩
    unfold greedyStep
    by_cases h : Ψt (π ++ [true]) < Ψt (π ++ [false])
    · simp only [h, decide_true]
      have h' : (Ψt (π ++ [true]) : ℝ) < Ψt (π ++ [false]) := by exact_mod_cast h
      rw [hc1, hc0] at h'
      have h'' := lt_of_mul_lt_mul_left h' hc.le
      linarith
    · simp only [h, decide_false]
      have h' : (Ψt (π ++ [false]) : ℝ) ≤ Ψt (π ++ [true]) := by exact_mod_cast not_lt.mp h
      rw [hc1, hc0] at h'
      have h'' := le_of_mul_le_mul_left h' hc
      linarith

/-- `prop:sound` step (2): the `S` greedy rounds of `greedySeed` end at a seed of length `S` whose potential is at
most that of the empty prefix. -/
theorem greedySeed_le (S : ℕ) (Ψt : List Bool → ℚ) (Ψ : List Bool → ℝ) (c : ℝ) (hc : 0 < c)
    (hexact : ∀ π : List Bool, π.length ≤ S → (Ψt π : ℝ) = c * Ψ π)
    (hchild : ∀ π : List Bool, π.length < S →
      Ψ π = (Ψ (π ++ [true]) + Ψ (π ++ [false])) / 2) :
    (greedySeed S Ψt).length = S ∧ Ψ (greedySeed S Ψt) ≤ Ψ [] :=
  greedy_descent S Ψt Ψ c hc hexact hchild S le_rfl

namespace CellCall

variable (C : CellCall)

/-! ### Prefix arithmetic -/

theorem prefixValue_append (π : List Bool) (b : Bool) :
    prefixValue (π ++ [b]) = prefixValue π + (if b then 2 ^ π.length else 0) := by
  induction π with
  | nil => cases b <;> simp [prefixValue]
  | cons a π ih =>
    simp only [List.cons_append, prefixValue, ih, List.length_cons, pow_succ]
    split_ifs <;> ring

theorem prefixValue_lt (π : List Bool) : prefixValue π < 2 ^ π.length := by
  induction π with
  | nil => simp [prefixValue]
  | cons a π ih =>
    simp only [prefixValue, List.length_cons, pow_succ]
    split_ifs <;> omega

/-! ### The potential of `prop:sound` -/

/-- `lem:fourier`, paper/paper.tex: the mixed residual `R_1(z, ·)` read by the matrices
`D_{θ,ν}(z)`. -/
def residualOne (z : Fin C.ncol) : Cell C.seed.N → ℤ := (C.column z).residual 0

/-- `lem:fourier`, paper/paper.tex: the mixed residual `R_2(z, ·)`. -/
def residualTwo (z : Fin C.ncol) : Cell C.seed.N → ℤ := (C.column z).residual 1

/-- `def:mask`, paper/paper.tex: the mask of column `z` as a real `0/1` matrix. -/
def realMask (z : Fin C.ncol) : Cell C.seed.N → ℝ := fun c => (C.pointMask z c : ℝ)

/-- `prop:sound` step (1), paper/paper.tex: `Ψ(π) = Σ_{z ∈ Z} E[Φ_z | π]`, the sum over a set `Z`
of columns of the conditional potentials of `cor:conditional` at the prefix `π`. -/
noncomputable def potential (Z : Finset (Fin C.ncol)) (π : List Bool) : ℝ :=
  ∑ z ∈ Z, Cycle.conditionalPotential (G₁ := C.G 0) (G₂ := C.G 1) C.seed (C.residualOne z)
    (C.residualTwo z) (C.realMask z) π.length (prefixValue π)

/-- `prop:sound` step (2) with `imp:seed`, paper/paper.tex: the two one-bit
extensions of a prefix average to the prefix. -/
theorem potential_children (Z : Finset (Fin C.ncol)) (π : List Bool) (hπ : π.length < C.seedLength) :
    C.potential Z π = (C.potential Z (π ++ [true]) + C.potential Z (π ++ [false])) / 2 := by
  have hlt := prefixValue_lt π
  unfold potential
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  rw [Cycle.conditionalPotential_children (G₁ := C.G 0) (G₂ := C.G 1) C.seed (C.residualOne z)
    (C.residualTwo z) (C.realMask z) π.length (prefixValue π) hπ]
  simp only [List.length_append, List.length_singleton, prefixValue_append, if_true,
    Bool.false_eq_true, if_false, add_zero, Nat.mod_eq_of_lt hlt]
  ring

/-- `cor:conditional`, paper/paper.tex: a complete prefix fixes the seed, so the conditional
potential is the potential `Φ_z` of the generated sample list. -/
theorem conditionalPotential_complete (z : Fin C.ncol) (pre : ℕ) (hpre : pre < 2 ^ C.seedLength) :
    Cycle.conditionalPotential (G₁ := C.G 0) (G₂ := C.G 1) C.seed (C.residualOne z) (C.residualTwo z)
        (C.realMask z) C.seedLength pre =
      Cycle.columnPotential (G₁ := C.G 0) (G₂ := C.G 1) (C.residualOne z) (C.residualTwo z)
        (C.realMask z) (Cycle.seedSample C.seed pre) := by
  have hpre' : pre < 2 ^ Cycle.seedLength C.seed := hpre
  unfold Cycle.conditionalPotential
  simp [seedLength, NearCubicWires.WireExponent3_5.Sampler.completion, Nat.mod_eq_of_lt hpre']

theorem realMask_abs_le (z : Fin C.ncol) (c : Cell C.seed.N) : |C.realMask z c| ≤ 1 := by
  unfold realMask pointMask
  rcases Mask.mask_zero_or_one ((C.column z).structural c) (C.column z).tau ((C.column z).X c) with h | h <;>
    simp [h]

/-- `prop:sound` step (2), paper/paper.tex: the potential of the empty prefix is the
independent-sample mean (`cor:conditional`), which `lem:tracebound` bounds, in the direct walk-moment form
`2 |Z| I C_8 Q^4 N^{13}` with `I = 2 |Θ|`. -/
theorem potential_empty_le (Z : Finset (Fin C.ncol)) (hN : 1 ≤ C.seed.N) (hNQ : C.seed.N ≤ C.seed.Q) :
    C.potential Z [] ≤
      2 * ((Z.card : ℝ) * (2 * (omega 4 (C.G 0) * omega 4 (C.G 1))) *
        NearCubicWires.WireExponent3_5.Sampler.C8 * (C.seed.Q : ℝ) ^ 4 * (C.seed.N : ℝ) ^ 13) := by
  have h := Sampler.mean_paperPotential_le hN hNQ
    (Sampler.matrixDictionary (G₁ := C.G 0) (G₂ := C.G 1) (Z := Z)
      (fun z => C.residualOne z) (fun z => C.residualTwo z) (fun z => C.realMask z))
    (Sampler.matrixDictionary_bounded _ _ _ (fun z c => C.realMask_abs_le z c))
  simp_rw [Sampler.paperPotential_eq_sum_columnPotential] at h
  rw [Sampler.matrixDictionary_card] at h
  have hcard : (Fintype.card Z : ℝ) = Z.card := by rw [Fintype.card_coe]
  rw [hcard] at h
  refine le_trans (le_of_eq ?_) (by push_cast at h ⊢; exact h)
  unfold potential
  simp only [List.length_nil, prefixValue]
  rw [← Finset.sum_coe_sort Z]
  simp_rw [Cycle.conditionalPotential_empty]
  unfold uMean
  rw [← Finset.sum_div, Finset.sum_comm]

/-! ### (4) Per-column intervals -/

/-- `prop:sound` step (4), paper/paper.tex: `V(z) = N^{-2} Σ_{u,v} pred(c(z) ⊕ u ⊕ v)`. -/
noncomputable def columnAcceptance (z : Fin C.ncol) : ℝ :=
  (∑ u, ∑ v, (bitInt (C.pred z (u, v)) : ℝ)) / (C.seed.N : ℝ) ^ 2

/-- `imp:partition`, paper/paper.tex, as used at `prop:sound`: since a uniform column and a
uniform point give a uniform input, `p_true = n_col^{-1} Σ_z V(z)`. -/
def PartitionAverage (p : ℚ) : Prop :=
  (p : ℝ) = (∑ z, C.columnAcceptance z) / C.ncol

/-- `(pred · mask)(z, c)` as a real number. -/
def maskedAccept (z : Fin C.ncol) (c : Cell C.seed.N) : ℝ :=
  ((bitInt (C.pred z c) * C.pointMask z c : ℤ) : ℝ)

/-- `lem:fourier`, paper/paper.tex, for the call: coefficients `F̂(θ, ν)` of total mass at most
`M_F` and unimodular selectors `a_{z,θ,ν}`, `b_{z,θ,ν}` with
`pred(c(z) ⊕ u ⊕ v) · mask(z,u,v) = Σ F̂ a(u) b(v) M_θ(z)[u,v]`, where `M_θ(z)` carries the mask inside. -/
structure FourierRows where
  Index : Type
  [fintypeIndex : Fintype Index]
  frequency : Index → Frequency 4 (C.G 0) (C.G 1)
  coefficient : Index → ℂ
  mass : (∑ t, ‖coefficient t‖) ≤ C.MF
  left : Fin C.ncol → Index → Fin C.seed.N → ℂ
  right : Fin C.ncol → Index → Fin C.seed.N → ℂ
  left_le : ∀ z t i, ‖left z t i‖ ≤ 1
  right_le : ∀ z t i, ‖right z t i‖ ≤ 1
  row : ∀ z u v, ((C.maskedAccept z (u, v) : ℝ) : ℂ) =
    Sampler.selectedRow coefficient (left z) (right z)
      (fun t u v => Sampler.maskedPhase (frequency t) (C.residualOne z) (C.residualTwo z)
        (C.realMask z) (u, v)) u v

attribute [instance] FourierRows.fintypeIndex

/-- `sec:params` item 4 and `lem:root`, paper/paper.tex: the sampler parameters.
`budget` is the rule `Q ≥ 1024 N m η^{-2} (4N²I)^{1/m}` with `m = 4` and `I = 2|Θ|`, raised to the fourth power
(the comparison of integer powers prescribed at `sec:params`). -/
structure SamplerBudget : Prop where
  two_le_N : 2 ≤ C.seed.N
  N_le_Q : C.seed.N ≤ C.seed.Q
  eta_nonneg : 0 ≤ C.η
  budget : (4096 : ℝ) ^ 4 * 4 * ((2 * (omega 4 (C.G 0) * omega 4 (C.G 1)) : ℕ) : ℝ) *
      (C.seed.N : ℝ) ^ 6 ≤ (C.seed.Q : ℝ) ^ 4 * (C.η : ℝ) ^ 8

/-- `prop:sound` step (1), paper/paper.tex: the printed sums are a fixed positive multiple of the
conditional potentials over the certified columns, at every prefix of length at most `S`. -/
def PotentialsExact : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ π : List Bool, π.length ≤ C.seedLength →
    (C.printedPotential π : ℝ) = c * C.potential C.certifiedColumns π

theorem pointMask_mem (z : Fin C.ncol) (c : Cell C.seed.N) :
    C.pointMask z c = 0 ∨ C.pointMask z c = 1 :=
  Mask.mask_zero_or_one _ _ _

theorem bitInt_mem (b : Bool) : bitInt b = 0 ∨ bitInt b = 1 := by
  cases b <;> simp [bitInt]

/-- The pointwise form of `V_m ≤ V ≤ V_m + 1 - μ` (`prop:sound`, paper/paper.tex). -/
theorem maskedAccept_le (z : Fin C.ncol) (c : Cell C.seed.N) :
    C.maskedAccept z c ≤ (bitInt (C.pred z c) : ℝ) ∧
      (bitInt (C.pred z c) : ℝ) ≤ C.maskedAccept z c + 1 - C.realMask z c := by
  unfold maskedAccept realMask
  rcases C.pointMask_mem z c with h | h <;> rcases bitInt_mem (C.pred z c) with g | g <;>
    simp [h, g]

theorem sampledAccept_cast (S : Fin C.seed.Q → Cell C.seed.N) (z : Fin C.ncol) :
    (C.sampledAccept S z : ℝ) = (∑ j, C.maskedAccept z (S j)) / C.seed.Q := by
  unfold sampledAccept maskedAccept
  push_cast
  rfl

theorem sampledMask_cast (S : Fin C.seed.Q → Cell C.seed.N) (z : Fin C.ncol) :
    (C.sampledMask S z : ℝ) = (∑ j, C.realMask z (S j)) / C.seed.Q := by
  unfold sampledMask realMask
  push_cast
  rfl

/-- `prop:sound` step (4), paper/paper.tex: given average sampler errors at most `2M_Fη` for the
masked predicate and at most `η` for the mask over a set `Z` of columns, `Lo ≤ p_true ≤ Hi`. -/
theorem interval_of_errors (Z : Finset (Fin C.ncol)) (S : Fin C.seed.Q → Cell C.seed.N) (p : ℚ)
    (hN : 1 ≤ C.seed.N) (hp : C.PartitionAverage p)
    (hV : (∑ z ∈ Z, |Sampler.averagingError (C.maskedAccept z) S|) ≤ Z.card * (2 * C.MF * C.η))
    (hμ : (∑ z ∈ Z, |Sampler.averagingError (C.realMask z) S|) ≤ Z.card * C.η) :
    (C.lower Z S : ℝ) ≤ p ∧ (p : ℝ) ≤ C.upper Z S := by
  have hN2 : (0 : ℝ) < (C.seed.N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ C.seed.N := by exact_mod_cast hN
    positivity
  -- column quantities
  set V : Fin C.ncol → ℝ := C.columnAcceptance with hVdef
  set Vm : Fin C.ncol → ℝ := fun z => (∑ u, ∑ v, C.maskedAccept z (u, v)) / (C.seed.N : ℝ) ^ 2
  set μ : Fin C.ncol → ℝ := fun z => (∑ u, ∑ v, C.realMask z (u, v)) / (C.seed.N : ℝ) ^ 2
  have hcount : (∑ _u : Fin C.seed.N, ∑ _v : Fin C.seed.N, (1 : ℝ)) / (C.seed.N : ℝ) ^ 2 = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  have hVlow : ∀ z, Vm z ≤ V z := by
    intro z
    simp only [Vm, hVdef, columnAcceptance]
    apply div_le_div_of_nonneg_right _ hN2.le
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (C.maskedAccept_le z (u, v)).1
  have hVup : ∀ z, V z ≤ Vm z + 1 - μ z := by
    intro z
    simp only [Vm, μ, hVdef, columnAcceptance]
    rw [← hcount]
    rw [← add_div, ← sub_div]
    apply div_le_div_of_nonneg_right _ hN2.le
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro u _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun v _ => (C.maskedAccept_le z (u, v)).2
  have hV0 : ∀ z, 0 ≤ V z := by
    intro z
    simp only [hVdef, columnAcceptance]
    apply div_nonneg _ hN2.le
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
      rcases bitInt_mem (C.pred z (u, v)) with g | g <;> simp [g]
  have hV1 : ∀ z, V z ≤ 1 := by
    intro z
    simp only [hVdef, columnAcceptance]
    rw [← hcount]
    apply div_le_div_of_nonneg_right _ hN2.le
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
      rcases bitInt_mem (C.pred z (u, v)) with g | g <;> simp [g]
  -- sampler errors
  have herrV : ∀ z, Sampler.averagingError (C.maskedAccept z) S = Vm z - C.sampledAccept S z := by
    intro z
    rw [C.sampledAccept_cast]
    rfl
  have herrμ : ∀ z, Sampler.averagingError (C.realMask z) S = μ z - C.sampledMask S z := by
    intro z
    rw [C.sampledMask_cast]
    rfl
  -- split the column sum
  have hsplit : (∑ z, V z) = (∑ z ∈ Z, V z) + ∑ z ∈ Finset.univ \ Z, V z := by
    rw [← Finset.sum_sdiff (Finset.subset_univ Z)]
    ring
  have hcompl : ((Finset.univ \ Z).card : ℝ) = C.ncol - Z.card := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin,
      Nat.cast_sub (by simpa using Finset.card_le_univ Z)]
  have hlowZ : (∑ z ∈ Z, (C.sampledAccept S z : ℝ)) - Z.card * (2 * C.MF * C.η) ≤ ∑ z ∈ Z, V z := by
    have : ∀ z ∈ Z, (C.sampledAccept S z : ℝ) - |Sampler.averagingError (C.maskedAccept z) S| ≤ V z := by
      intro z _
      have h1 := neg_abs_le (Sampler.averagingError (C.maskedAccept z) S)
      rw [herrV z] at h1 ⊢
      linarith [hVlow z]
    have hs := Finset.sum_le_sum this
    rw [Finset.sum_sub_distrib] at hs
    linarith
  have hupZ : (∑ z ∈ Z, V z) ≤ (∑ z ∈ Z, ((C.sampledAccept S z : ℝ) + 1 - C.sampledMask S z)) +
      Z.card * (2 * C.MF * C.η) + Z.card * C.η := by
    have : ∀ z ∈ Z, V z ≤ ((C.sampledAccept S z : ℝ) + 1 - C.sampledMask S z) +
        |Sampler.averagingError (C.maskedAccept z) S| + |Sampler.averagingError (C.realMask z) S| := by
      intro z _
      have h1 := le_abs_self (Sampler.averagingError (C.maskedAccept z) S)
      have h2 := neg_abs_le (Sampler.averagingError (C.realMask z) S)
      rw [herrV z] at h1 ⊢
      rw [herrμ z] at h2 ⊢
      linarith [hVup z]
    have hs := Finset.sum_le_sum this
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
    linarith
  have hrest0 : 0 ≤ ∑ z ∈ Finset.univ \ Z, V z := Finset.sum_nonneg fun z _ => hV0 z
  have hrest1 : (∑ z ∈ Finset.univ \ Z, V z) ≤ C.ncol - Z.card := by
    rw [← hcompl]
    have := Finset.sum_le_sum (s := Finset.univ \ Z) fun z _ => hV1 z
    simpa using this
  have hp' : (p : ℝ) = (∑ z, V z) / C.ncol := hp
  rcases Nat.eq_zero_or_pos C.ncol with h0 | hpos
  · -- no columns: every quantity divides by zero
    have hc0 : (C.ncol : ℝ) = 0 := by exact_mod_cast h0
    have : (p : ℝ) = 0 := by rw [hp', hc0, div_zero]
    unfold lower upper
    push_cast
    rw [this, hc0]
    simp
  · have hncol : (0 : ℝ) < C.ncol := by exact_mod_cast hpos
    unfold lower upper
    push_cast
    rw [hp']
    constructor
    · apply div_le_div_of_nonneg_right _ hncol.le
      rw [hsplit]
      nlinarith [hlowZ, hrest0]
    · apply div_le_div_of_nonneg_right _ hncol.le
      rw [hsplit]
      nlinarith [hupZ, hrest1]

/-! ### Outward rounding and the default -/

/-- Step 5 and `prop:sound`, paper/paper.tex: outward rounding to multiples of `2^{-n}`
preserves an interval containing `p`, so `|p̂ - p| ≤ κ̂`. -/
theorem centerRadius_contains (n : ℕ) (lo hi p : ℚ) (hlo : lo ≤ p) (hhi : p ≤ hi) :
    |(centerRadius n lo hi).1 - p| ≤ (centerRadius n lo hi).2 := by
  have hpos : (0 : ℚ) < 2 ^ n := by positivity
  have hf : dyadicFloor n lo ≤ lo := by
    apply (div_le_iff₀ hpos).mpr
    exact Int.floor_le (lo * 2 ^ n)
  have hc : hi ≤ dyadicCeil n hi := by
    apply (le_div_iff₀ hpos).mpr
    exact Int.le_ceil (hi * 2 ^ n)
  rw [abs_sub_le_iff]
  dsimp only [centerRadius]
  constructor <;> linarith

theorem columnAcceptance_mem (hN : 1 ≤ C.seed.N) (z : Fin C.ncol) :
    0 ≤ C.columnAcceptance z ∧ C.columnAcceptance z ≤ 1 := by
  have hN2 : (0 : ℝ) < (C.seed.N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ C.seed.N := by exact_mod_cast hN
    positivity
  have hb : ∀ u v, 0 ≤ (bitInt (C.pred z (u, v)) : ℝ) ∧ (bitInt (C.pred z (u, v)) : ℝ) ≤ 1 := by
    intro u v
    rcases bitInt_mem (C.pred z (u, v)) with g | g <;> simp [g]
  unfold columnAcceptance
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => (hb u v).1) hN2.le
  · rw [div_le_one hN2]
    calc (∑ u, ∑ v, (bitInt (C.pred z (u, v)) : ℝ)) ≤ ∑ _u : Fin C.seed.N, ∑ _v : Fin C.seed.N, (1 : ℝ) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (hb u v).2
      _ = (C.seed.N : ℝ) ^ 2 := by simp [sq]

/-- `prop:sound`, paper/paper.tex: `p_true ∈ [0, 1]`, so the sound default `(1/2, 1/2)` contains it. -/
theorem soundDefault_contains (p : ℚ) (hN : 1 ≤ C.seed.N) (hp : C.PartitionAverage p) :
    |soundDefault.1 - p| ≤ soundDefault.2 := by
  have h0 : (0 : ℝ) ≤ (∑ z, C.columnAcceptance z) / C.ncol :=
    div_nonneg (Finset.sum_nonneg fun z _ => (C.columnAcceptance_mem hN z).1) (Nat.cast_nonneg _)
  have h1 : (∑ z, C.columnAcceptance z) / C.ncol ≤ (1 : ℝ) := by
    rcases Nat.eq_zero_or_pos C.ncol with h | h
    · have hc0 : (C.ncol : ℝ) = 0 := by exact_mod_cast h
      rw [hc0, div_zero]; norm_num
    · have hc : (0 : ℝ) < C.ncol := by exact_mod_cast h
      rw [div_le_one hc]
      calc (∑ z, C.columnAcceptance z) ≤ ∑ _z : Fin C.ncol, (1 : ℝ) :=
            Finset.sum_le_sum fun z _ => (C.columnAcceptance_mem hN z).2
        _ = C.ncol := by simp
  have hp0 : (0 : ℚ) ≤ p := by exact_mod_cast (hp ▸ h0 : (0 : ℝ) ≤ p)
  have hp1 : p ≤ 1 := by exact_mod_cast (hp ▸ h1 : (p : ℝ) ≤ 1)
  simp only [soundDefault]
  rw [abs_le]
  constructor <;> linarith

/-! ### (3) The sampler error of the chosen seed -/

/-- `prop:sound` steps (2)–(3), paper/paper.tex: if the printed sums are exact (step (1)), the
seed chosen greedily has potential over the certified columns at most the `lem:tracebound` bound. -/
theorem chosenSeed_potential_le (hN : 1 ≤ C.seed.N) (hNQ : C.seed.N ≤ C.seed.Q)
    (hexact : C.PotentialsExact) :
    (∑ z ∈ C.certifiedColumns, Cycle.columnPotential (G₁ := C.G 0) (G₂ := C.G 1) (C.residualOne z)
        (C.residualTwo z) (C.realMask z) C.samples) ≤
      2 * ((C.certifiedColumns.card : ℝ) * (2 * (omega 4 (C.G 0) * omega 4 (C.G 1))) *
        NearCubicWires.WireExponent3_5.Sampler.C8 * (C.seed.Q : ℝ) ^ 4 * (C.seed.N : ℝ) ^ 13) := by
  obtain ⟨c, hc, hex⟩ := hexact
  obtain ⟨hlen, hle⟩ := greedySeed_le C.seedLength C.printedPotential (C.potential C.certifiedColumns) c hc
    hex (fun π hπ => C.potential_children C.certifiedColumns π hπ)
  have hfin : C.potential C.certifiedColumns C.chosenSeed =
      ∑ z ∈ C.certifiedColumns, Cycle.columnPotential (G₁ := C.G 0) (G₂ := C.G 1) (C.residualOne z)
        (C.residualTwo z) (C.realMask z) C.samples := by
    unfold potential
    apply Finset.sum_congr rfl
    intro z _
    have hl : C.chosenSeed.length = C.seedLength := hlen
    have hlt : prefixValue C.chosenSeed < 2 ^ C.seedLength := hl ▸ prefixValue_lt C.chosenSeed
    rw [hl, C.conditionalPotential_complete z _ hlt]
    rfl
  rw [← hfin]
  exact hle.trans (C.potential_empty_le C.certifiedColumns hN hNQ)

theorem uMean_coe_sort (Z : Finset (Fin C.ncol)) (f : Fin C.ncol → ℝ) :
    uMean (fun z : Z => f z) = (∑ z ∈ Z, f z) / Z.card := by
  unfold uMean
  rw [Finset.sum_coe_sort Z f, Fintype.card_coe]

/-- `prop:sound` step (3), paper/paper.tex, with `lem:selector` and `lem:root`: the average errors of
the masked predicate and of the mask over the certified columns are at most `2M_Fη` and `η`. -/
theorem certified_errors_le (F : C.FourierRows) (hB : C.SamplerBudget) (hexact : C.PotentialsExact) :
    (∑ z ∈ C.certifiedColumns, |Sampler.averagingError (C.maskedAccept z) C.samples|) ≤
        C.certifiedColumns.card * (2 * C.MF * C.η) ∧
      (∑ z ∈ C.certifiedColumns, |Sampler.averagingError (C.realMask z) C.samples|) ≤
        C.certifiedColumns.card * C.η := by
  set Z := C.certifiedColumns with hZ
  rcases Z.eq_empty_or_nonempty with he | hne
  · simp [he]
  have hN1 : 1 ≤ C.seed.N := le_trans (by norm_num) hB.two_le_N
  haveI : Nonempty Z := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hpot := C.chosenSeed_potential_le hN1 hB.N_le_Q hexact
  rw [← hZ] at hpot
  have hS : Sampler.paperPotential (Sampler.matrixDictionary (G₁ := C.G 0) (G₂ := C.G 1) (Z := Z)
      (fun z => C.residualOne z) (fun z => C.residualTwo z) (fun z => C.realMask z)) C.samples ≤
      2 * ((Fintype.card Z : ℝ) * Fintype.card (Frequency 4 (C.G 0) (C.G 1) × Fin 2) *
        NearCubicWires.WireExponent3_5.Sampler.C8 * (C.seed.Q : ℝ) ^ 4 * (C.seed.N : ℝ) ^ 13) := by
    rw [Sampler.paperPotential_eq_sum_columnPotential, Sampler.matrixDictionary_card, Fintype.card_coe,
      Finset.sum_coe_sort Z (fun z => Cycle.columnPotential (G₁ := C.G 0) (G₂ := C.G 1) (C.residualOne z)
        (C.residualTwo z) (C.realMask z) C.samples)]
    refine hpot.trans (le_of_eq ?_)
    push_cast
    ring
  have hQη : 4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 *
      Fintype.card (Frequency 4 (C.G 0) (C.G 1) × Fin 2) * (C.seed.N : ℝ) ^ 5 ≤
        (C.seed.Q : ℝ) ^ 4 * (C.η : ℝ) ^ 8 := by
    apply Sampler.paper_budget_implies_direct hB.two_le_N
    rw [Sampler.matrixDictionary_card]
    exact hB.budget
  have hη : (0 : ℝ) ≤ C.η := by exact_mod_cast hB.eta_nonneg
  have hmask := Sampler.average_mask_error (G₁ := C.G 0) (G₂ := C.G 1) (Z := Z) hN1 hB.N_le_Q
    (fun z => C.residualOne z) (fun z => C.residualTwo z) (fun z => C.realMask z) C.samples hS
    (C.η : ℝ) hη hQη
  have hpred := Sampler.average_masked_predicate_error (G₁ := C.G 0) (G₂ := C.G 1) (Z := Z)
    (Λ := F.Index) hN1 hB.N_le_Q
    (fun z => C.residualOne z) (fun z => C.residualTwo z) (fun z => C.realMask z)
    (fun z c => (bitInt (C.pred z c) : ℝ)) C.samples hS (C.η : ℝ) (C.MF : ℝ) hη hQη
    F.frequency F.coefficient F.mass (fun z => F.left z) (fun z => F.right z)
    (fun z => F.left_le z) (fun z => F.right_le z)
    (fun z u v => by
      have h := F.row z u v
      rw [← h]
      unfold maskedAccept realMask
      push_cast
      rfl)
  have hfun : ∀ z : Fin C.ncol, (fun x => (bitInt (C.pred z x) : ℝ) * C.realMask z x) = C.maskedAccept z := by
    intro z
    funext x
    unfold maskedAccept realMask
    push_cast
    rfl
  simp_rw [hfun] at hpred
  rw [C.uMean_coe_sort Z (fun z => |Sampler.averagingError (C.maskedAccept z) C.samples|)] at hpred
  rw [C.uMean_coe_sort Z (fun z => |Sampler.averagingError (C.realMask z) C.samples|)] at hmask
  have hcard : (0 : ℝ) < Z.card := by exact_mod_cast hne.card_pos
  constructor
  · rw [div_le_iff₀ hcard] at hpred
    linarith
  · rw [div_le_iff₀ hcard] at hmask
    linarith

/-- **`prop:sound` from its step (1)**, paper/paper.tex: for every cell call whose printed sums are
exact multiples of the conditional potentials, the returned `(p̂, κ̂)` satisfies `|p̂ - p_true| ≤ κ̂`, where
`p_true` is the average of the column acceptances (`imp:partition`). The hypotheses are `lem:fourier` for the call
(`FourierRows`), the sampler rule of `sec:params` (`SamplerBudget`), and step (1) (`PotentialsExact`). -/
theorem sound_of_exact_potentials (p : ℚ) (hp : C.PartitionAverage p) (F : C.FourierRows)
    (hB : C.SamplerBudget) (hexact : C.PotentialsExact) :
    |C.run.1 - p| ≤ C.run.2 := by
  have hN1 : 1 ≤ C.seed.N := le_trans (by norm_num) hB.two_le_N
  unfold run
  split_ifs with hcons
  · obtain ⟨hV, hμ⟩ := C.certified_errors_le F hB hexact
    obtain ⟨hlo, hhi⟩ := C.interval_of_errors C.certifiedColumns C.samples p hN1 hp hV hμ
    exact centerRadius_contains C.n _ _ p (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  · exact C.soundDefault_contains p hN1 hp

/-! ### (1) Exact conditional potentials -/

/-- `cor:conditional`, paper/paper.tex: the printed walk weight is `2^S c_π(w)`. -/
theorem walkWeight_real (π : List Bool) (hπ : π.length ≤ C.seedLength)
    (w : Cycle.Walk C.seed.N traceOrder) :
    (C.walkWeight π w : ℝ) =
      2 ^ C.seedLength * (Cycle.conditionalGamma C.seed π.length (prefixValue π) w : ℝ) := by
  have h := Cycle.scaledGamma_spec C.seed π.length (prefixValue π) hπ w
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  unfold walkWeight
  rw [← h']
  rfl

/-- `lem:cycle`, paper/paper.tex: the real walk mask of the cycle identity is the integer walk mask. -/
theorem walkMask_real (z : Fin C.ncol) (w : Cycle.Walk C.seed.N traceOrder) :
    Cycle.walkMask traceOrder_pos (C.realMask z) w = (C.walkMask z w : ℝ) := by
  unfold Cycle.walkMask walkMask Walks.walkMaskInt realMask pointMask
  push_cast
  rfl

/-- Proof of `prop:sound` step (1) on the printed sums, paper/paper.tex: on the certified columns,
`Ψ̃(π) = Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_w 2^S c_π(w) mask_w(z) 1[Y_{1,σ} = 0] 1[Y_{2,σ} = 0]`. -/
theorem printedPotential_walks (H : C.ReconstructionHypotheses) (π : List Bool)
    (hπ : π.length ≤ C.seedLength) :
    C.printedPotential π = ∑ z ∈ C.certifiedColumns, ∑ σ : Cycle.SignPattern traceOrder,
      (Cycle.kappa traceOrder σ : ℚ) * ∑ w, (C.walkWeight π w : ℚ) * (C.walkMask z w : ℚ) *
        ((if Cycle.walkSum traceOrder_pos ((C.column z).residual 0) σ w = 0 then 1 else 0) *
          (if Cycle.walkSum traceOrder_pos ((C.column z).residual 1) σ w = 0 then 1 else 0)) := by
  unfold printedPotential
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hκ : Cycle.kappa traceOrder σ = 0
  · simp [hκ]
  · rw [C.sum_reconstructedValue H π hπ z hz σ hκ]

/-- **`prop:sound` step (1)**, paper/paper.tex: with `cor:conditional`,
`Ψ̃(π) = 2^S (4^m / 2|Θ|) Ψ(π)` at every prefix of length at most `S`. -/
theorem potentialsExact (H : C.ReconstructionHypotheses) : C.PotentialsExact := by
  have hΘ : (0 : ℝ) < Fintype.card (Frequency 4 (C.G 0) (C.G 1)) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨(4 : ℝ) ^ 4 * 2 ^ C.seedLength / (2 * Fintype.card (Frequency 4 (C.G 0) (C.G 1))),
    by positivity, ?_⟩
  intro π hπ
  rw [C.printedPotential_walks H π hπ]
  unfold potential
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro z _
  rw [Cycle.conditional_cycle_sum_identity (G₁ := C.G 0) (G₂ := C.G 1) C.seed (C.residualOne z)
    (C.residualTwo z) (C.realMask z) (H.residual_le z 0) (H.residual_le z 1)]
  simp_rw [C.walkMask_real z]
  -- both sides are `2^S Σ_w Σ_σ c_π(w) mask_w(z) κ_σ 1[Y_1 = 0] 1[Y_2 = 0]`
  have hw : ∀ w : Cycle.Walk C.seed.N traceOrder,
      (C.walkWeight π w : ℝ) = 2 ^ C.seedLength *
        (Cycle.conditionalGamma C.seed π.length (prefixValue π) w : ℝ) := C.walkWeight_real π hπ
  simp_rw [hw]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro σ _
  unfold residualOne residualTwo
  simp only [apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one, Rat.cast_zero]
  field_simp

/-- **`prop:sound`** (Soundness for every witness), paper/paper.tex: on every cell call, the
returned `(p̂, κ̂)` satisfies `|p̂ - p_true| ≤ κ̂`. The hypotheses are `imp:partition` (`PartitionAverage`),
`lem:fourier` for the call (`FourierRows`), the sampler rule of `sec:params` (`SamplerBudget`), and the
reconstruction hypotheses (`ReconstructionHypotheses`: `lem:residue`'s modulus bound, `lem:identity`,
`imp:window` on the boxes and the parameter facts of `sec:params`). -/
theorem prop_sound (p : ℚ) (hp : C.PartitionAverage p) (F : C.FourierRows) (hB : C.SamplerBudget)
    (H : C.ReconstructionHypotheses) :
    |C.run.1 - p| ≤ C.run.2 :=
  C.sound_of_exact_potentials p hp F hB (C.potentialsExact H)

end CellCall

end NearQuarticWires.Algorithm
